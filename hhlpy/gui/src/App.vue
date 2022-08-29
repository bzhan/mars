<template>
  <div id="app">
    <div class="toolbar">
      <Toolbar ref="toolbar" :editorView="editorView"
        @openDocument="openDocument"
        @verifyVCs="verifyVCs" />
    </div>

    <div id="main">
      <Resizer :initialLeftWidth="20"> 
        <template v-slot:left>
          <FileBrowser ref="fileBrowser" :path="[]" />
        </template>
        <template v-slot:right>
        <Resizer :initialLeftWidth="50"> 
          <template v-slot:left>
            <Editor ref="editor" @docChanged="docChanged" />
          </template>
          <template v-slot:right>
            <VerificationCondition2 ref="vcs" :editorView="editorView" />
            <ErrorDisplay ref="errorDisplay" />
          </template>
        </Resizer>
        </template>
      </Resizer>
    </div>
  </div>
</template>

<script>
import Editor from './components/Editor.vue'
import Resizer from './components/Resizer.vue'
import Toolbar from './components/Toolbar.vue'
import VerificationCondition2 from "./components/VerificationCondition2.vue"
import ErrorDisplay from './components/ErrorDisplay.vue'
import FileBrowser from './components/FileBrowser.vue'
import { serverConnection } from './serverConnection.js'

export default {
  name: 'App',
  components: {
    Resizer, Toolbar, Editor, VerificationCondition2, ErrorDisplay, FileBrowser
  },
  data: () => { return {
    editorView : null,
  }},
  mounted: function () {

    this.editorView = this.$refs.editor.initEditor();

    serverConnection.socket.addEventListener("open", () => {
      this.$refs.toolbar.socketOpened()
    });

    serverConnection.socket.addEventListener("message", (event) => {
      let eventData = JSON.parse(event.data)
      console.log(event)
      
      if (eventData.type === "computed"){
        this.$refs.vcs.computed(eventData)
      }
      else if(eventData.type === 'verified'){
        this.$refs.vcs.verified(eventData)
      }
      else if(eventData.type === 'example_list'){
        this.$refs.toolbar.examples = eventData.examples;
      }
      else if (eventData.type ===  'computation_process_ready'){
        this.$refs.toolbar.computationProcessReady = true;
      }
      else if(eventData.type === 'load_file'){
        this.openDocument(eventData.code);
      }
      else if(eventData.type === 'error'){
        this.$refs.errorDisplay.addError(eventData.error);
        console.error("Server error:", eventData.error);
      } else if(eventData.type !== 'file_list'){
        this.$refs.errorDisplay.addError(`Unknown message type: ${eventData.type}`);
        console.error("Unknown message type:", eventData.type);
      }
    })
  },
  methods: {
    openDocument(doc) {
      this.$refs.vcs.outdated = true;
      this.editorView = this.$refs.editor.initEditor(doc);
      serverConnection.socket.send(JSON.stringify({code: doc, type: "compute"}));
    },
    verifyVCs() {
      this.$refs.vcs.verifyVCs();
    },
    docChanged() {
      this.$refs.vcs.outdated = true;
      // Compute VCSs
      let code = this.editorView.state.doc.toString();
      serverConnection.socket.send(JSON.stringify({code: code, type: "compute"}));
    }
  }
}
</script>

<style>

html,
body,
#app {
  height: 100%;
  margin: 0;
  font-family: Avenir, Helvetica, Arial, sans-serif;
}

#app {
  display: flex;
  flex-flow: column;
  height: 100%;
  font-size: 120%;
  overflow:hidden;
}

#main {
  flex: 1 1 auto;
  overflow:hidden;
}

.toolbar {
  flex: 0 1 auto;
}
</style>
