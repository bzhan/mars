<template>
<span>
<span class="annotation-button" v-on:click="OpenMenu">
  {{ buttonName }}
</span>
<span v-if="menuOpen" v-on:click="add">dI</span>
<span></span>
</span>
</template>

<script>
export default {
  name: 'AnnotationButton',
  props: [],
  data() {
    return {
      buttonName: '',
      menuOpen: false
    }
  },
  methods: {
    addAnnotation: function () {
      this.$emit("addAnnotation")
    },
    openMenu: function(){
      this.menuOpen = true
    },
  }
}
</script>

<!-- Add "scoped" attribute to limit CSS to this component only -->
<style scoped>
.annotation-button {
  border-radius: 20px;
  background: #60911b;
  padding: 0 5px;
  color:white;
  font-weight: bold;
  font-family: Avenir, Helvetica, Arial, sans-serif;
  font-size: smaller;
  cursor: pointer;
}
</style>
