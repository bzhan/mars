<template>
  <div class="toolbar">
    <div class="group">
      <button v-on:click="newFile">New</button>
      <span v-if="savingDialog">
        Enter file name:
        <input type="text" v-model="savingName"/>
      </span>
      <button v-on:click="saveFile">Save</button>
    </div>
  </div>
</template>

<script>
import { useWebsocketStore } from '../stores/websocket'
import { useOpenFilesStore } from '../stores/openFiles'
import { onMounted, ref } from '@vue/composition-api'

export default {
  setup() {
    const websocketStore = useWebsocketStore()
    const openFilesStore = useOpenFilesStore()
    const savingDialog = ref(false)
    const savingName = ref("")
    function saveFile () {
      if (this.savingDialog) {
        this.savingDialog = true
        openFilesStore.saveFile(savingName.value)
      } else {
        if (openFilesStore.files[openFilesStore.activeTab].new) {
          this.savingDialog = true
        } else {
          openFilesStore.saveFile()
        }
      }
    }
    function newFile () {
      openFilesStore.newFile()
    }

    onMounted(() => {
      websocketStore.reconnect()
    })
 
    return {
      websocketStore,
      openFilesStore,
      saveFile,
      newFile,
      savingDialog,
      savingName
    }
  }
}

</script>

<!-- Add "scoped" attribute to limit CSS to this component only -->
<style scoped>
.toolbar {
  background: rgb(67, 67, 67);
  color: white;
}

.toolbar .group {
  display: inline-block;
  margin-right: 20px;
} 

.toolbar button {
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

.toolbar button:hover {
  color: white;
  border: solid 2px #fff;
}

</style>
