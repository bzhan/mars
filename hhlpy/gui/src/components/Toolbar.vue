<template>
  <div class="toolbar">
    <div class="group">
      <button v-on:click="newFile">New</button>
      <button v-on:click="saveFile">Save</button> {{websocketStore.connected}}
    </div>
  </div>
</template>

<script>
import { useWebsocketStore } from '../stores/websocket'
import { useOpenFilesStore } from '../stores/openFiles'
import { onMounted } from '@vue/composition-api'

export default {
  setup() {
    const websocketStore = useWebsocketStore()
    const openFilesStore = useOpenFilesStore()
    function saveFile () {
      openFilesStore.saveFile()
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
      newFile
    }
  }
}

</script>

<!-- Add "scoped" attribute to limit CSS to this component only -->
<style scoped>
.toolbar {
  background: rgb(67, 67, 67);
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
