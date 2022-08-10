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
          <div class="pages">
            <div class="tabs">
              <span class="tab" v-for="file in openFiles" :key="file" 
                :class="{open: file == currentTab}"
                @click="currentTab = file">
                {{file}}
                <v-icon name="times" scale="1" fill="#888" class="close" @click="closeFile(file)"></v-icon>
              </span>
              
            </div>
            <div class="page">
              <Page v-for="file in openFiles" v-bind:key="file" v-show="file == currentTab" :file="file" 
                ref="pages"/>
            </div>
          </div>
        </template>
      </Resizer>
    </div>
  </div>
</template>

<script>
import 'vue-awesome/icons'
import Icon from 'vue-awesome/components/Icon'
import Resizer from './components/Resizer.vue'
import FileBrowser from './components/FileBrowser.vue'
import Page from './components/Page.vue'
import Toolbar from './components/Toolbar.vue'
import { serverConnection } from './serverConnection.js'
import EventBus from './EventBus'

export default {
  name: 'App',
  components: {
    Resizer, Page, FileBrowser, Toolbar,
    'v-icon': Icon
  },
  data: () => { return {
    openFiles: [],
    currentTab: null
  }},
  mounted: function () {

    serverConnection.socket.addEventListener("open", () => {
      this.$refs.toolbar.socketOpened()
    });

    EventBus.$on("loadFile", (file) => {
      this.openDocument(file);
    })

    EventBus.$on("saveFile", () => {
      for (let page of this.$refs.pages) {
        if (page.file === this.currentTab) {
          page.saveFile()
        }
      }
    })

    serverConnection.socket.addEventListener("message", (event) => {
      let eventData = JSON.parse(event.data)
      console.log(event)
      
      if(eventData.type === 'example_list'){
        this.$refs.toolbar.examples = eventData.examples;
      }
      else if (eventData.type ===  'computation_process_ready'){
        this.$refs.toolbar.computationProcessReady = true;
      }
      else if(eventData.type === 'error'){
        // this.$refs.errorDisplay.addError(eventData.error);
        // console.error("Server error:", eventData.error);
      }
    })
  },
  methods: {
    openDocument(file) {
      console.log(this.openFiles);
      if (!this.openFiles.includes(file)) {
        this.openFiles = [...this.openFiles, file];
      }
      this.currentTab = file;
    },
    closeFile(file){
      this.openFiles = this.openFiles.filter((f) => f !== file)
    },
    verifyVCs() {
      // this.$refs.vcs.verifyVCs();
    },
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

.pages {
  display: flex;
  flex-flow: column;
  height: 100%;
  overflow:hidden;
}

.tab {
  display: inline-block;
  background: #ccc;
  margin: 0 1px;
  padding: 10px;
  width: 200px;
  text-align: center;
  cursor: default;
}

.close {
  float:right;
  padding: 8px 0;
}

.tab.open {
  background: white;
}

#main {
  flex: 1 1 auto;
  overflow:hidden;
}

.page {
  flex: 1 1 auto;
  overflow:hidden;
}

.toolbar {
  flex: 0 1 auto;
}

.tabs {
  flex: 0 1 auto;
}
</style>
