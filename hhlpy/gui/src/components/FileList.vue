<template>
  <div class="fileList">
    <div v-for="(dir) in dirs" :key="dir">
      <div @click="toggleDir(dir)" class="dir" >
        <v-icon name="angle-right" scale="1" v-if="!open[dir]"></v-icon>
        <v-icon name="angle-down" scale="1" v-if="open[dir]"></v-icon>
        {{ dir }}
      </div>
      <FileList v-if="open[dir]" :path="[...path, dir]" />
    </div>
    <div :class="`file supported-${supported[file]}`" v-for="file in files" :key="file" @click="openFile(file)">
      <v-icon name="align-left" scale="1" fill="#12a" v-if="supported[file]"></v-icon>
      <v-icon name="question" scale="1" fill="#888" v-if="!supported[file]"></v-icon>
      {{ file }}
    </div>
  </div>
</template>

<script>
import Vue from 'vue'
import 'vue-awesome/icons'
import Icon from 'vue-awesome/components/Icon'
import { serverConnection } from '../serverConnection.js'

export default {
  name: 'FileList',
  components: {
    'v-icon': Icon
  },
  props: {
    path: Array,
  },
  data: () => { return {
    files: [],
    dirs: [],
    open: {},
    supported: {},
  }},
  mounted: function() {
    if (serverConnection.socket.readyState == WebSocket.OPEN) {
      this.socketOpened()
    } else {
      serverConnection.socket.addEventListener("open", () => {
        this.socketOpened()
      })
    }
  },
  methods: {
    openFile: function(file){
      serverConnection.socket.send(JSON.stringify({example: [...this.path, file].join("/"), type: "load_file"}));
    },
    toggleDir: function(dir) {
      Vue.set(this.open, dir, !this.open[dir]);
    },
    socketOpened: function () {
      serverConnection.socket.addEventListener("message", (event) => {
        let eventData = JSON.parse(event.data)
        if(eventData.type === 'file_list' && eventData.path == this.path.join("/")){
          this.dirs = eventData.dirs;
          console.log(this.dirs)
          for (let dir in this.dirs) {
            Vue.set(this.open, this.dirs[dir], false);
          }
          this.files = eventData.files;
          for (let file in this.files) {
            Vue.set(this.supported, this.files[file], this.files[file].endsWith(".hhl"));
          }
        }
      });
      serverConnection.socket.send(JSON.stringify({type: "get_file_list", path:this.path.join("/")}))
    },
    loadExample: function (e) {
      serverConnection.socket.send(JSON.stringify({example: e.target.value, type: "load_file"}));
    }
  }
}
</script>

<!-- Add "scoped" attribute to limit CSS to this component only -->
<style scoped>
.fileList {
  margin-left:5px;
  padding-left:10px;
}
.dir:hover, .file:hover {
  background: #ddd
}
.supported-false {
  color: #888;
}
</style>
