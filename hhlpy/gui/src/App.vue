<template>
  <div id="app">
    <div class="toolbar">
      <Toolbar ref="toolbar" />
    </div>

    <div id="main">
      <Resizer :initialLeftWidth="20"> 
        <template v-slot:left>
          <FileBrowser ref="fileBrowser" :path="[]" />
        </template>
        <template v-slot:right>
          <div class="pages">
            <div class="tabs">
              <span class="tab" v-for="(file, fileName) in openFilesStore.files" :key="fileName" 
                :class="{open: fileName == openFilesStore.activeTab}"
                @click="openFilesStore.activeTab = fileName">
                {{fileName}}
                <v-icon name="times" scale="1" fill="#888" class="close"
                  @click="openFilesStore.closeFile(fileName)"></v-icon>
              </span>
              
            </div>
            <div class="page">
              <Page v-for="(file, fileName) in openFilesStore.files" v-bind:key="fileName" 
                v-show="fileName == openFilesStore.activeTab" :file="file" 
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
import { mapStores } from 'pinia'
import { useOpenFilesStore } from './stores/openFiles'

export default {
  name: 'App',
  components: {
    Resizer, Page, FileBrowser, Toolbar,
    'v-icon': Icon
  },
  data: () => { return {
  }},
  computed: {
    ...mapStores(useOpenFilesStore)
  },
  mounted: function () {

  },
  methods: {

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
