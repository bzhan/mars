<template>
  <div class="editor">
    <h1>HHLPy</h1>
    <div><input type="text" v-model="pre"></div>
    <div id="code"></div>
    <div><input type="text" v-model="post"></div>
    <button v-on:click="compute">Compute</button>
    <button v-on:click="verify">Verify</button>
  </div>
</template>

<script>
import {EditorState, EditorView, basicSetup} from "@codemirror/basic-setup"
import {HCSP} from "../grammar/hcsp"
import {indentWithTab} from "@codemirror/commands"
import {keymap} from "@codemirror/view"
import { displayVerificationCondition, getPosition, removeVerificationCondition } from "../decoration/verification_condition"
import { test_examples } from "../test_examples/examples"

function initEditor(){
  const editorView = new EditorView({
    state: EditorState.create({
      doc: test_examples.e4.hp,
      extensions: [basicSetup, keymap.of([indentWithTab]), HCSP()]
    }),
    parent: document.getElementById("code")
  });
  return editorView;
}

export default {
  name: 'Editor',
  data: () => { return {
    pre : test_examples.e4.pre,
    post : test_examples.e4.post,
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
          console.log("vcs:", this.vcs)

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
    compute: function () {
      let pre = this.pre
      let post = this.post
      let hp = this.editorView.state.doc.toString();
      
      this.socket.send(JSON.stringify({pre: pre, hp: hp, post:post, type: "compute"}));
      console.log({pre: pre, hp: hp, post:post});
    },
    verify: function () {
      for (let vc in this.vc_infos) {
        this.socket.send(JSON.stringify({vc: vc, solver: this.vc_infos[vc].solver, type: "verify"}))
      }
    },
    display_vc_infos : function() {
      removeVerificationCondition(this.editorView)
      console.log("vc_infos1:", this.vc_infos)

      for (let i in this.vcs){
        let vcData = this.vcs[i]
        let lineNumber = vcData.line
        let linePos = getPosition(this.editorView, lineNumber)
        let solver = 'Z3'
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
        displayVerificationCondition(this.editorView, vcData.vc, linePos, changeSolverCallBack, solver, result)
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
</style>
