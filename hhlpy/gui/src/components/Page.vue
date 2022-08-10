<template>
  <div class="page">
    <Resizer :initialLeftWidth="50"> 
      <template v-slot:left>
        <Editor ref="editor" @docChanged="docChanged" :file="file" />
      </template>
      <template v-slot:right>
        <ErrorDisplay ref="errorDisplay" />
        <VerificationCondition2 ref="vcs" :editorView="editorView" :file="file" />
      </template>
    </Resizer>
  </div>
</template>

<script>
import Editor from './Editor.vue'
import Resizer from './Resizer.vue'
import VerificationCondition2 from "./VerificationCondition2.vue"
import ErrorDisplay from './ErrorDisplay.vue'
import { serverConnection } from '../serverConnection.js'

export default {
  name: 'Page',
  props: {
    file: String,
  },
  components: {
    Resizer, Editor, VerificationCondition2, ErrorDisplay
  },
  data: () => { return {
    editorView : null,
  }},
  mounted: function () {

    serverConnection.socket.send(JSON.stringify({file: this.file, type: "load_file"}));

    serverConnection.socket.addEventListener("message", (event) => {
      let eventData = JSON.parse(event.data)
      console.log(event)
      
      if (eventData.type === "computed" && eventData.file == this.file){
        this.$refs.vcs.computed(eventData)
      }
      else if(eventData.type === 'verified' && eventData.file == this.file){
        this.$refs.vcs.verified(eventData)
      }
      else if(eventData.type === 'load_file' && eventData.file == this.file){
        this.editorView = this.$refs.editor.initEditor(eventData.code);
        this.docChanged()
      }
      else if(eventData.type === 'error'){
        this.$refs.errorDisplay.addError(eventData.error);
        console.error("Server error:", eventData.error);
      }
    })
  },
  methods: {
    verifyVCs() {
      this.$refs.vcs.verifyVCs();
    },
    docChanged() {
      this.$refs.vcs.outdated = true;
      // Compute VCSs
      let code = this.editorView.state.doc.toString();
      serverConnection.socket.send(JSON.stringify({code: code, type: "compute", file: this.file}));
    }
  }
}
</script>

<style>
.page {
  height: 100%;
}
</style>
