<template>
  <div class="verification-condition" >
    <span class="vc-formula">
      {{ vcFormula }}
    </span> 

    <select v-model="vcSolver" @change="changeSolver" class="vc-button">
      <option>Z3</option>
      <option>Wolfram Engine</option>
    </select>

    <span class="vc-icon">
      <v-icon name="check-circle" style="fill:green" v-show="vcResult === true" scale="1.5"></v-icon>
      <v-icon name="times-circle" style="fill:red" v-show="vcResult === false" scale="1.5"></v-icon>
    </span>

  </div>
</template>

<script>
import 'vue-awesome/icons'
import Icon from 'vue-awesome/components/Icon'

export default {
  name: 'VerificationCondition',
  props: [],
  data() {
    return {
      vcFormula: '',
      vcSolver: "Z3",
      vcResult: ''
    }
  },
  methods: {
    changeSolver() {
      this.$emit("changeSolver", this.vcSolver)
    }
  },
  components: {
    'v-icon': Icon
  }
}
</script>

<!-- Add "scoped" attribute to limit CSS to this component only -->
<style scoped>
.verification-condition {
  padding: 5px 0px;
  display: block;
}
.vc-formula {
  border-radius: 20px;
  background: #1b6a91;
  padding: 0 5px;
  color:white;
  font-weight: bold;
  font-family: Avenir, Helvetica, Arial, sans-serif;
  font-size: smaller;
  /* display: inline-block; */
}

.vc-button {
  border-radius: 20px;
  background: #60911b;
  padding: 0 5px;
  color:white;
  font-weight: bold;
  font-family: Avenir, Helvetica, Arial, sans-serif;
  font-size: smaller;
  cursor: pointer;
}

.vc-icon {
  vertical-align: middle;
  margin: 0 20px
}

</style>