<template>
  <div id="app">
    <div class="toolbar">
      <Toolbar ref="toolbar" :socket="socket" :editorView="editorView"
        @openDocument="openDocument"
        @verifyVCs="verifyVCs" />
    </div>

    <div id="main">
      <Resizer> 
        <template v-slot:left>
          <Editor ref="editor" />
        </template>
        <template v-slot:right>
          <ErrorDisplay ref="errorDisplay" />
          <VerificationCondition2 ref="vcs" :socket="socket" :editorView="editorView" />
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

export default {
  name: 'App',
  components: {
    Resizer, Toolbar, Editor, VerificationCondition2, ErrorDisplay
  },
  data: () => { return {
    socket: null,
    editorView : null,
  }},
  mounted: function () {

    this.editorView = this.$refs.editor.initEditor();

    const wsPath = "ws://localhost:8000"

    const openConnection = () => {
      this.socket = new WebSocket(wsPath);

      this.socket.onopen = () => {
        this.$refs.toolbar.socketOpened()
      }

      this.socket.onmessage = (event) => {
        let eventData = JSON.parse(event.data)
        console.log(event)
        
        if (eventData.type === "computed"){
          this.$refs.vcs.computed(eventData.vcs)
        }
        else if(eventData.type === 'verified'){
          this.$refs.vcs.verified(eventData)
        }
        else if(eventData.type === 'example_list'){
          this.$refs.toolbar.examples = eventData.examples;
        }
        else if(eventData.type === 'load_example'){
          console.log("load ex");
          this.editorView = this.$refs.editor.initEditor(eventData.code);
        }
        else if(eventData.type === 'error'){
          this.$refs.errorDisplay.addError(eventData.error);
          console.error("Server error:", eventData.error);
        } else {
          this.$refs.errorDisplay.addError(`Unknown message type: ${eventData.type}`);
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
    openDocument(doc) {
      this.editorView = this.$refs.editor.initEditor(doc);
    },
    verifyVCs() {
      this.$refs.vcs.verifyVCs();
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
