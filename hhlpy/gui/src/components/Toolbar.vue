<template>
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
</template>

<script>
import { EditorView } from 'codemirror';

export default {
  name: 'Toobar',
  props: {
    socket: WebSocket,
    editorView: EditorView
  },
  data: () => { return {
    examples: []
  }},
  methods: { 
    socketOpened: function () {
      this.socket.send(JSON.stringify({type: "get_example_list"}))
    },
    openFile: function (e) {
      e.target.files[0].text().then((doc) => {
        this.$emit("openDocument", doc);
      })
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
      this.$emit("verifyVCs");
    },
  }
}
</script>

<!-- Add "scoped" attribute to limit CSS to this component only -->
<style scoped>
.toolbar {
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

</style>
