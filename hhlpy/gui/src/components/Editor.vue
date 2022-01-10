<template>
  <div class="editor">
    <h1>HHLPy</h1>
    <div><input type="text" v-model="pre"></div>
    <div id="code"></div>
    <div><input type="text" v-model="post"></div>
    <button v-on:click="run">Run</button>
    <div class="vcs">{{vcs}}</div>
  </div>
</template>

<script>
import {EditorState, EditorView, basicSetup} from "@codemirror/basic-setup"

function initEditor(){
  const editorView = new EditorView({
    state: EditorState.create({
      doc: "x := x+1.23456",
      extensions: [basicSetup]
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
    vcs: ""
  }},
  mounted: function () {

    this.editorView = initEditor();

    this.socket = new WebSocket("ws://localhost:8000");
    
    this.socket.onopen = () => {
      console.log("Connection opened")
    };

    this.socket.onmessage = (event) => {
      this.vcs = event.data;
    };
  },
  methods: {
    run : function () {
      let pre = this.pre
      let post = this.post
      let hp = this.editorView.state.doc.toString();
      this.socket.send(JSON.stringify({pre: pre, hp: hp, post:post}));
      console.log({pre: pre, hp: hp, post:post});
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
}

input {
  font-family: monospace;
}

.vcs {
  margin-top: 20px;
  font-family: monospace;
}
</style>
