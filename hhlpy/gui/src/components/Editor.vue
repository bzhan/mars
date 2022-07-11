<template>
  <div class="editor">
    <div id="code"></div>
    <div class="toolbar">
      <div class="group">
        <form class="open_file">
          <label for="open_file">Open file</label>
          <input type="file" id="open_file" name="open_file" accept=".hhl" v-on:change="openFile">
        </form>
        <select v-on:change="loadExample">
          <option disabled selected>Load example</option>
          <option v-for="example in examples" :value="example" :key="example">
            {{ example }}
          </option>
        </select>
      </div>
      <div class="group">
        <button v-on:click="compute">Compute</button>
        <button v-on:click="verify">Verify</button>
      </div>
    </div>
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

const fixedHeightEditor = EditorView.theme({
  "&": {height: "100%", overflow: "hidden"},
  ".cm-scroller": {overflow: "auto"}
})

function initEditorState(doc){
  return EditorState.create({
    doc: doc,
    extensions: [basicSetup, keymap.of([indentWithTab]), HCSP(), originField, originTheme, fixedHeightEditor]
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
    vc_infos: {},
    examples: []
  }},
  mounted: function () {

    this.editorView = initEditor();

    const wsPath = "ws://localhost:8000"

    const openConnection = () => {
      this.socket = new WebSocket(wsPath);
      
      this.socket.onopen = () => {
        console.log("Connection opened");

        this.socket.send(JSON.stringify({type: "get_example_list"}))
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
        }
        else if(eventData.type === 'example_list'){
          this.examples = eventData.examples;
        }
        else if(eventData.type === 'load_example'){
          this.editorView.setState(initEditorState(eventData.code));
        }
        else if(eventData.type === 'error'){ 
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
    loadExample: function (e) {
      this.socket.send(JSON.stringify({example: e.target.value, type: "load_example"}));
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
  display: flex;
  flex-flow: column;
  height: 100%;
  font-size: 120%;
}

.toolbar {
  flex: 0 1 auto;
  background: rgb(67, 67, 67);
}

#code {
  flex: 1 1 auto;
  overflow: hidden;
}

.toolbar form {
  display: inline;
}

.toolbar .group {
  display: inline-block;
  margin-right: 20px;
} 

.toolbar button, 
.toolbar select, 
.toolbar .open_file label {
  font-size: 100%;
  margin: 2px;
  padding: 2px 10px;
  border-radius: 20px;
  border: solid 2px #ddd;
  color: #ddd;
  background: rgb(67, 67, 67);
  font-family: sans-serif;
  font-weight: bold;
  cursor: pointer;
}

.toolbar button:hover, 
.toolbar .open_file label:hover {
  color: white;
  border: solid 2px #fff;
}

.open_file input {
  opacity: 0;
  width: 0;
}

.vcs {
  margin-top: 20px;
  font-family: monospace;
}
</style>
