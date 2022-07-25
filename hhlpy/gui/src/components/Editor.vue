<template>
  <div class="editor">
    <div class="main"  @mouseup="isDragging = false" @mousemove="resizeH">
      <div id="code" width="60%"></div>
      <div class="resizer" @mousedown="isDragging = true"></div>
      <vcs :vc_infos="vc_infos" :view="editorView" @changeSolver="changeSolver" class="vcs"></vcs>
    </div>

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
    editorView: initEditor(),
    examples: [],
    isDragging: false
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
        console.log("Connection opened");

        this.socket.send(JSON.stringify({type: "get_example_list"}))
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
      // Send the doc in editor to server with type "compute".
      let code = this.editorView.state.doc.toString();
      this.socket.send(JSON.stringify({code: code, type: "compute"}));
    },
    verify: function () {
      // Send the computed vc formula, the index i and the choosen solver to server.
      for (let i = 0; i < this.vc_infos.length; i++){
        let formula = this.vc_infos[i].formula
        let solver = this.vc_infos[i].solver
        // we need to send the code to let the server know about the function definitions
        let code = this.editorView.state.doc.toString();
        this.socket.send(JSON.stringify({index: i, formula: formula, solver: solver, code: code, type: "verify"}))
      }
    },
    // Add vc informations in this.vc_infos
    add_vc_infos: function(){
      for (let i in this.vc_info_received){
        let vcData = this.vc_info_received[i]  // vcData is object
        let label = vcData.label
        let solver = "z3"
        
        if (vcData.method){
          solver = vcData.method
        }

        this.vc_infos.push({
          index: i,
          formula: vcData.formula,
          assume: vcData.assume,
          show: vcData.show,
          label: label,
          solver: solver,  //TODO: set the solver
          result: null,
          origin: vcData.origin,
          pred_end_pos: vcData.pred_end_pos,
          pms_start_pos: vcData.pms_start_pos,
          pms_end_pos: vcData.pms_end_pos
        })
      }
    },

    changeSolver(data) {
      let index = data.index
      // The label of the verification condition of which solver is changed.
      let label = this.vc_infos[index].label
      // The new solver
      let solver = data.solver     

      let pms_start_pos = this.vc_infos[index].pms_start_pos
      let pms_end_pos = this.vc_infos[index].pms_end_pos
      let old_proof_methods = this.editorView.state.sliceDoc(pms_start_pos+2, pms_end_pos-2)
      console.log("old_proof_methods:", old_proof_methods)

      // Transfer the proof method string into a dictionary.
      let pm_dict = this.to_proof_method_dict(old_proof_methods)
      
      // Set the value on label as solver
      pm_dict.set(label, solver)
      console.log("pm_dict:", pm_dict)

      let new_proof_methods = this.to_proof_method_string(pm_dict)

      // Change the document in the editor into new_proof_methods
      this.editorView.dispatch(this.editorView.state.update({
        changes: {from: pms_start_pos, to: pms_end_pos, insert: "{{" + new_proof_methods + "}}"}}))

      // The proof method start position and end position of each verification condition
      // may be changed after inserting.
      // Therefore call the compute() function to get the new position.
      // TODO: is there a better solution?
      this.compute()
    },

    to_proof_method_dict(pms)
    /* Transfer a proof method string into a Map object.
       Example: transfer "init: z3, maintain: wolfram" 
                into Map([[init, z3], [maintain, wolfram]])
       Note that if the proof method is "z3", without label, 
       the key for it would be set as "None" in the Map object.  **/    
    {
      console.assert(typeof(pms) === "string", "The parameter should be a string")
      pms = pms.trim()
      let pm_dict = new Map()

      if (pms === ""){
        return pm_dict
      }

      else{
        // pm_list is, for example ["init: z3", "maintain: wolfram"]
        let pm_list = pms.split(",")

        console.log("pm_list:", pm_list)

        for (let pm of pm_list){
          let key, value
          // Case when pm is with a label, set the key as label
          if (pm.includes(":")){
            key = pm.split(":")[0].trim()
            value = pm.split(":")[1].trim()
          }
          // Case when pm is without a label, set the key as None
          else{
            key = "None"
            value = pm.trim()
          }
          pm_dict.set(key, value)
        }

        return pm_dict
      }
    },

    to_proof_method_string(pm_dict)
    /* Transfer a proof method Map object into a string.
       Example: transfer Map([[init, z3], [maintain, wolfram]])
                into "init: z3, maintain: wolfram"
       Note that if the key is "None" in the Map object, for example, Map([["None", "z3"],])
       the string for it would be only the method, without a label, i.e. "z3". */  
    {
      let pm_str = ""
      let i = 0
      let end_str = ", "
      for (let [key, value] of pm_dict){
        // Each "key: value" ends with ", " except the last one.
        console.log(i)
        if (i === pm_dict.size - 1){
          end_str = ""
        }
        i ++;
        
        if (key === "None"){
          pm_str += value + end_str
        }
        else{
          pm_str += key + ": " + value + end_str
        }
      }

      return pm_str
    },

    resizeH(e) {
      /*Resize horizontally 
      TODO: wrap this in a component?*/
      if (!this.isDragging){
        return false
      }

      let resizer = document.querySelector('.resizer')
      let container = resizer.parentNode
      let itemLeft = resizer.previousElementSibling

      let itemLeftMinWidth = 200
      let resizerWidth = 5

      let pointerRelativeXpos = e.clientX - container.offsetLeft

      itemLeft.style.width = (Math.max(itemLeftMinWidth, pointerRelativeXpos - resizerWidth)) + 'px'
      itemLeft.style.flexGrow = 0
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

.main {
  display: flex;
  flex-direction: row;
  flex: 1 1 auto;
  overflow: hidden;
}

#code {
  box-sizing: border-box;
  flex: 1 1 auto;
}
.vcs {
  box-sizing: border-box;
  flex: 1 1 auto;
  overflow: scroll;
}

.resizer {
    width: 5px;
    padding: 0;
    cursor: ew-resize;
    flex: 0 0 auto;
}

.resizer:hover {
  background: lightgray;
}
</style>
