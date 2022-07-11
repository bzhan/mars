<template>
  <div class="editor">
    <div id="code"></div>

    <vcs :vc_infos="vc_infos" :view="editorView"></vcs>
    <!-- {{vc_infos}} -->

    <div class="toolbar">
      <div class="group">
        <form class="open_file">
          <label for="open_file">Open file</label>
          <input type="file" id="open_file" name="open_file" accept=".hhl" v-on:change="openFile">
        </form>
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
import { test_examples } from "../test_examples/examples"
import { originTheme, originField } from '../decoration/origin'
import VerificationCondition2 from "./VerificationCondition2.vue"

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
    vc_info_received: "",   //An  array received from server, consisted of objects about vc information.
    vc_infos: [], // An array of verification condition information, each information object include formula, solver, result and origin.
    editorView: initEditor()
  }},
  components: {
    vcs: VerificationCondition2
  },
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
          this.vc_info_received = eventData.vcs;
          // Clear the old vc information.
          this.vc_infos = []
          // Add the new vc information computed.
          this.add_vc_infos()
        }
        else if(eventData.type === 'verified'){
          let i = eventData.index
          let formula = eventData.formula
          let result = eventData.result
          
          if(formula ===  this.vc_infos[i].formula)
            // Variable result stores the result of formula with index i.
            // Set the result of index i as the value of variable result.
            this.vc_infos[i].result = result
          else{
             console.error("Wrong result for the verification condition:", formula)
          }
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
    compute: function () {
      // Send the doc in editor to server with type "compute".
      let code = this.editorView.state.doc.toString();
      
      this.socket.send(JSON.stringify({code: code, type: "compute"}));
    },
    verify: function () {
      // Send the computed vc formula, the index i and the choosen solver to server.
      for (let i = 0; i < this.vc_infos.length; i++){
        let formula = this.vc_infos[i].formula
        let solver = this.vc_infos[i].solver
        this.socket.send(JSON.stringify({index: i, formula: formula, solver: solver, type: "verify"}))
      }
    },
    // Add vc informations in this.vc_infos
    add_vc_infos: function(){
      for (let i in this.vc_info_received){
        let vcData = this.vc_info_received[i]  // vcData is object
        this.vc_infos.push({
          formula: vcData.formula,
          solver: "Z3",  //TODO: set the solver
          result: null,
          origin: vcData.origin
        })
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
  font-size: 20pt;
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
.toolbar .open_file label {
  font-size: 20pt;
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
