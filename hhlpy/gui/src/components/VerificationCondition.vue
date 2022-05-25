<template>
  <div class="verification-condition" >
    <span class="vc-formula">
      {{ vcFormula }}
    </span> 

    <select v-model="vcSolver" @change="changeSolver" class="vc-button">
      <option>Z3</option>
      <option>Wolfram Engine</option>
    </select>

    <span>
      {{ vcResult }}
    </span>

    <v-icon name="check" style="color:green"></v-icon>

    <span>
      <v-icon name="check-circle" style="color:green"></v-icon>
    </span>
    <span>
      <v-icon name="times" style="color:red"></v-icon>
    </span>
    <span>
      <v-icon name="times-circle" style="color:red"></v-icon>
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
  display: inline-block;
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

.vc-check {
  color: green
}

.fa-icon {
color: green;  
}

</style>
