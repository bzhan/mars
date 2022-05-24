<template>
  <div class="verification-condition" >
    <span class="vc-formula">
      {{ vcFormula }}
    </span> 

    <select v-model="vcSolver" @change="changeSolver">
      <option disabled>Select One Verification Tool</option>
      <option>Z3</option>
      <option>Wolfram Engine</option>
    </select>

    <span>
      {{ vcResult }}
    </span>
  </div>
</template>

<script>
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
</style>
