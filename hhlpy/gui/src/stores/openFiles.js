import { ref } from '@vue/composition-api';
import { defineStore, mapStores } from 'pinia'
import Vue from 'vue';
import { useWebsocketStore } from './websocket';

const defaultContent = "pre [true];\nskip;\npost[true];\n"

export const useOpenFilesStore = defineStore('openFiles', {
  state: () => ({ 
    files: {},
    newFileCounter: 0,
    activeTab: null,
    initializedListeners: false
  }),
  getters: {
    ...mapStores(useWebsocketStore)
  },
  actions: {
    newFile() {
      this.newFileCounter++;
      let name = `*Untitled${this.newFileCounter}.hhl`
      Vue.set(this.files, name, {name: name, new: true, content: ref(defaultContent)})
      this.activeTab = name
    },
    openFile(file) {
      if (!this.files[file]) {
        Vue.set(this.files, file, {name: file, new: false, content: ref(null)})
      }
      this.activeTab = file
      this.websocketStore.send({file: file, type: "load_file"})
      this.initializeListeners()
    },
    saveFile(fileName) {
      let code = this.files[this.activeTab].content
      if (!fileName) {
        fileName = this.activeTab
      }
      this.websocketStore.send({file: fileName, code: code, type: "save_file"});
    },
    closeFile(file) {
      Vue.delete(this.files, file)
    },
    initializeListeners() {
      if (!this.initializedListeners) {
        this.websocketStore.addListener("load_file", (data) => {
          if (this.files[data.file]) {
            this.files[data.file].content = data.code
          }
        })
        this.initializedListeners = true
      }
    }
  },
})
