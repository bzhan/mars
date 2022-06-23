<template>
  <div class="editor">
    <h1>HHLPy</h1>
    <div id="code"></div>

    <button v-on:click="compute">Compute</button>
    <button v-on:click="verify">Verify</button>

    <br/>
    <br/>
    <form class="open_file">
      <label for="open_file">Open file</label>
      <input type="file" id="open_file" name="open_file" accept=".hhl" v-on:change="openFile">
    </form>

    <div>{{ vcs }}</div>
  </div>
</template>

<script>
import {EditorState, EditorView, basicSetup} from "@codemirror/basic-setup"
import {HCSP} from "../grammar/hcsp"
import {indentWithTab} from "@codemirror/commands"
import {keymap} from "@codemirror/view"
import { displayVerificationCondition, getPosition, removeVerificationCondition } from "../decoration/verification_condition"
import { test_examples } from "../test_examples/examples"
import { originTheme, originField } from '../decoration/origin'

function initEditorState(doc){
  return EditorState.create({
    doc: doc,
    extensions: [basicSetup, keymap.of([indentWithTab]), HCSP(), originField, originTheme]
  })
}

function initEditor(doc){
  if (!doc){
    doc = test_examples.e4
  }
  const editorView = new EditorView({
    state: initEditorState(doc),
    parent: document.getElementById("code")
  });
  return editorView;
}

export default {
  name: 'Editor',
  data: () => { return {
    vcs: "",
    vc_infos: {}
  }},
  mounted: function () {

    this.editorView = initEditor();

    const wsPath = "ws://localhost:8000"

    const openConnection = () => {
      this.socket = new WebSocket(wsPath);
      
      this.socket.onopen = () => {
        console.log("Connection opened")
      };

      this.socket.onmessage = (event) => {
        let eventData = JSON.parse(event.data)
        if (eventData.type === "computed"){
          this.vcs = eventData.vcs;

          this.display_vc_infos()
        }
        else if(eventData.type === 'verified'){
          console.log("eventData:", eventData)
          let vc = eventData.vc
          let result = eventData.vc_result
          this.vc_infos[vc].result = result

          this.display_vc_infos()
        } else if(eventData.type === 'error'){ 
          console.error("Server side error:", eventData.error)
        } else {
          console.error("Unknown message type:", eventData.type);
        }
      };
    }

    openConnection();

    // Regularly check if connection is still open. Otherwise, reconnect.
    setInterval(() => {
      if (this.socket.readyState !== 1) {
        console.log("Websocket not open. Attempting to reconnect.")
        openConnection();
      }
    }, 5000);

  },
  methods: { 
    openFile: function (e) {
      e.target.files[0].text().then(t => 
        this.editorView.setState(initEditorState(t))
      )
    },
    compute: function () {
      let code = this.editorView.state.doc.toString();
      
      this.socket.send(JSON.stringify({code: code, type: "compute"}));
    },
    verify: function () {
      for (let vc in this.vc_infos) {
        this.socket.send(JSON.stringify({vc: vc, solver: this.vc_infos[vc].solver, type: "verify"}))
      }
    },
    display_vc_infos : function() {
      // Remove the old verification condition
      removeVerificationCondition(this.editorView)

      for (let i in this.vcs){
        let vcData = this.vcs[i]
        let lineNumber = vcData.line
        let linePos = getPosition(this.editorView, lineNumber)

        let solver = 'Z3'
        let origin = vcData.origin
        let result
        if (this.vc_infos[vcData.vc]){
          solver = this.vc_infos[vcData.vc].solver
          result = this.vc_infos[vcData.vc].result
        }
        else {
          this.vc_infos[vcData.vc] = {"solver": solver, "result": null}
        }
        let changeSolverCallBack = (solver) => {
          this.vc_infos[vcData.vc].solver = solver
        }
        displayVerificationCondition(this.editorView, vcData.vc, linePos, changeSolverCallBack, solver, result, origin)
        console.log("vc_infos:", this.vc_infos)
      }
    }
  }
}
</script>

<!-- Add "scoped" attribute to limit CSS to this component only -->
<style scoped>
.editor {
  width: 900px;
  height: 300px;
  text-align: left;
  margin: auto;
  font-size: 20pt;
}

input {
  font-family: monospace;
  font-size: 20pt;
}

button {
  font-size: 20pt;
}

.vcs {
  margin-top: 20px;
  font-family: monospace;
}

.open_file input {
  opacity: 0;
}

.open_file label {
  background-color: #bcbcbc;
  padding: 5px 10px;
  border-radius: 5px;
  border: 1px ridge black;
  height: auto;
}
</style>
