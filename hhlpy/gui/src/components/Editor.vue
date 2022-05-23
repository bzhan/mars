<template>
  <div class="editor">
    <h1>HHLPy</h1>
    <div>
      <label for="z3">
      <input type="radio" id="z3" value="z3" v-model="solver">Z3
      </label>
      <label for="wol">
        <input type="radio" id="wol" value="wolfram_engine" v-model="solver">Wolfram Engine
      </label>
    </div>
    <div><input type="text" v-model="pre"></div>
    <div id="code"></div>
    <div><input type="text" v-model="post"></div>
    <button v-on:click="run">Run</button>
    <button v-on:click="parse">Parse</button>
    <div class="vcs">{{vcs}}</div>
  </div>
</template>

<script>
import {EditorState, EditorView, basicSetup} from "@codemirror/basic-setup"
import {HCSP} from "../grammar/hcsp"
import {parser} from "../grammar/hcsp_parser"
import {indentWithTab} from "@codemirror/commands"
import {keymap} from "@codemirror/view"
import { displayVerificationCondition, getPosition } from "../decoration/verification_condition"

function initEditor(){
  const editorView = new EditorView({
    state: EditorState.create({
      doc: "x := x+1.23456;\nif true\nthen skip\nelse y := 1\nendif; \
            \n<x_dot=1 & x < 5>\ninvariant [x >= 1]",
      extensions: [basicSetup, keymap.of([indentWithTab]), HCSP()]
    }),
    parent: document.getElementById("code")
  });
  return editorView;
}

export default {
  name: 'Editor',
  data: () => { return {
    pre : "x >= 0.12345",
    post : "x >= 1",
    vcs: "",
    solver: "z3"
  }},
  computed:{
    z3() {
      if (this.solver === "z3"){
        return true
      }
      else{
        return false
      }
    },
    wolfram_engine() {
      if (this.solver === "wolfram_engine"){
        return true
      }
      else{
        return false
      }
    }
  },
  mounted: function () {

    this.editorView = initEditor();

    this.socket = new WebSocket("ws://localhost:8000");
    
    this.socket.onopen = () => {
      console.log("Connection opened")
    };

    this.socket.onmessage = (event) => {
      this.vcs = JSON.parse(event.data);
      console.log("vcs:", this.vcs)
      for (let i in this.vcs){
        let vcData = this.vcs[i]
        let lineNumber = vcData.line
        let linePos = getPosition(this.editorView, lineNumber)
        displayVerificationCondition(this.editorView, vcData.vc, linePos)
      }
    };
  },
  methods: {
    run: function () {
      let pre = this.pre
      let post = this.post
      let hp = this.editorView.state.doc.toString();
      let z3 = this.z3.toString()
      let wolfram_engine = this.wolfram_engine.toString()
      this.socket.send(JSON.stringify({pre: pre, hp: hp, post:post, 
                                       z3: z3, wolfram_engine: wolfram_engine}));
      console.log({pre: pre, hp: hp, post:post, z3: z3, wolfram_engine: wolfram_engine});
    },
    parse: function () {
      console.log(parser)
      let p = parser.parse(this.editorView.state.doc.toString())
      console.log(p)
      console.log(p.toString())
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
