<template>
  <div class="fileBrowser">
    <FileList :socket="socket" :path="path" />
  </div>
</template>

<script>
import FileList from "./FileList.vue"

export default {
  name: 'FileBrowser',
  components: {
    'FileList': FileList
  },
  props: {
    socket: WebSocket,
    path: Array,
  },
}
</script>

<!-- Add "scoped" attribute to limit CSS to this component only -->
<style scoped>
.fileBrowser {
  background: #eee;
  overflow-x: hidden;
  cursor: default;
}
</style>
