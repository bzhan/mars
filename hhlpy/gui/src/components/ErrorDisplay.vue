<template>
  <div class="errors">

    <ul>
        <li v-for="error in errors" :key="error.id" class="error">
          <v-icon name="times" scale="1.5" class="close-button" @click="dismissError(error.id)"></v-icon>
          <div class="msg">{{error.msg}}</div>
        </li>
    </ul>
  </div>
</template>

<script>
import 'vue-awesome/icons'
import Icon from 'vue-awesome/components/Icon'

export default {
  name: 'ErrorDisplay',
  components: {
    'v-icon': Icon
  },
  data() {
    return {
      errors: [],
      counter: 0
    }
  },
  methods: {
    dismissError(id) {
      console.log(id)
      this.errors = this.errors.filter((error) => error.id != id)
    },
    addError(msg) {
      this.errors.push({msg, id: this.counter});
      this.counter++;
    }
  }
}
</script>

<!-- Add "scoped" attribute to limit CSS to this component only -->
<style scoped>
.errors ul {
  margin:0;
  padding:0;
}
.error {
  white-space: pre-wrap;
  border-radius: 20px;
  background: #e84412;
  padding: 7px;
  color:white;
  font-weight: bold;
  font-size: smaller;
  margin: 5px 0;
  /* display: inline-block; */
}
.msg {
  padding: 7px;
}
.close-button {
  float:right;
  fill:white;
  opacity: .9;
  display: block;
  padding: 7px;
}
.close-button:hover {
  opacity: 1;
  cursor: pointer;
}
</style>
