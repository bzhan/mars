<template>
  <div class="page">
    <Resizer :initialLeftWidth="50"> 
      <template v-slot:left>
        <Editor ref="editor" @docChanged="docChanged" :file="file.name" />
      </template>
      <template v-slot:right>
        <ErrorDisplay ref="errorDisplay" />
        <VerificationCondition ref="vcs" :editorView="editorView" :file="file.name" />
      </template>
    </Resizer>
  </div>
</template>

<script>
import Editor from './Editor.vue'
import Resizer from './Resizer.vue'
import VerificationCondition from "./VerificationCondition.vue"
import ErrorDisplay from './ErrorDisplay.vue'
import { useOpenFilesStore } from '../stores/openFiles'
import { mapStores } from 'pinia'
import { useWebsocketStore } from '../stores/websocket'

export default {
  name: 'Page',
  props: {
    file: Object,
  },
  watch: {
    "file.content": {
      handler (content) {
        if (content !== null && !this.editorView) {
          this.editorView = this.$refs.editor.initEditor(content);
          this.docChanged(content)
        }
      }
    }
  },
  components: {
    Resizer, Editor, VerificationCondition, ErrorDisplay
  },
  computed: {
    ...mapStores(useOpenFilesStore, useWebsocketStore)
  },
  data: () => { return {
    editorView : null,
  }},
  mounted: function () {
    if (this.file.content.value !== null) {
      this.editorView = this.$refs.editor.initEditor(this.file.content.value);
      this.docChanged(this.file.content.value);
    }
    this.websocketStore.addListener("computed", this.showComputed)
    this.websocketStore.addListener("verified", this.showVerified)
    this.websocketStore.addListener("error", this.showError)
  },
  beforeDestroy: function () {
    this.websocketStore.removeListener("computed", this.showComputed)
    this.websocketStore.removeListener("verified", this.showVerified)
    this.websocketStore.removeListener("error", this.showError)
  },
  methods: {
    showComputed(data) {
      if (data.file == this.file.name){
        this.$refs.vcs.computed(data)
      }
    },
    showVerified(data) {
      if (data.file == this.file.name){
        this.$refs.vcs.verified(data)
      }
    },
    showError(data) {
      if (!data.file || data.file == this.file.name){
        this.$refs.errorDisplay.addError(data.error);
        console.error("Server error:", data.error);
      }
    },
    verifyVCs() {
      this.$refs.vcs.verifyVCs();
    },
    docChanged(content) {
      if (content !== null) {
        this.$refs.vcs.outdated = true;
        //  Disable the function that compute automatically when listening to docChange. This is because it reacts slowly when changes are made consecutively to large programs.
        // // Compute VCSs
        // this.openFilesStore.files[this.file.name].content = content;
        // console.log("files:", this.openFilesStore.files)
        // this.websocketStore.send({code: content, type: "compute", file: this.file.name});
      }
    }
  }
}
</script>

<style>
.page {
  height: 100%;
}
</style>
