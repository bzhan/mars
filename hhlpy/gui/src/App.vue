<template>
  <div id="app">

    <file-browser v-on:change="changePath" :axiosConfig="{baseURL: 'http://localhost:8081'}" />
    <Editor/>
  </div>
</template>

<script>
import FileBrowser from "vuetify-file-browser";
import Editor from './components/Editor.vue'

export default {
  name: 'App',
  components: {
    Editor,
    FileBrowser
  },
  methods: {
    changePath: function (e) {
      console.log(e)
    }
  }
}
</script>

<style>
#app {
  font-family: Avenir, Helvetica, Arial, sans-serif;
  -webkit-font-smoothing: antialiased;
  -moz-osx-font-smoothing: grayscale;
  text-align: center;
  color: #2c3e50;
  margin-top: 60px;
}
</style>
