<!-- Verification Conditions, including the formula, solver and result -->
<template>
    <div class="verification-condition">
        <ul>
            <li v-for="vc_info in vc_infos" :key="vc_info.formula">
            <!-- TODO: change the key -->
                <span class="vc-icon">
                    <v-icon name="check-circle" style="fill:green" v-show="vc_info.result === true" scale="1.5"></v-icon>
                    <v-icon name="times-circle" style="fill:red" v-show="vc_info.result === false" scale="1.5"></v-icon>
                </span>

                <span class="vc-formula" @mouseover="showOrigin(vc_info.origin)" @mouseleave="hideOrigin">
                {{ vc_info.formula }}
                </span> 
                <!-- vc_info.solver(the solver in vc_infos in Editor.vue) is also changed by using v-model -->
                <select v-model="vc_info.solver" @change="changeSolver" class="vc-button">
                    <option>Z3</option>
                    <option>Wolfram Engine</option>
                </select>

            </li>
        </ul>
    </div>
</template>

<script>
import 'vue-awesome/icons'
import Icon from 'vue-awesome/components/Icon'
import { EditorView } from '@codemirror/view'
import { showOrigin, hideOrigin } from '../decoration/origin'

export default ({
    props: {
        vc_infos: Array,
        view: EditorView
    },

    data() {
      return{
      }
    },

    methods: {
    changeSolver() {
    //   this.$emit("changeSolver", this.vcSolver)
    },
    showOrigin(origin) {
      let effects = origin.map((range) => showOrigin.of(range));
      this.view.dispatch({effects});
    },
    hideOrigin() {
      let effects = [hideOrigin.of({})];
      this.view.dispatch({effects});
    }
  },
  components: {
    'v-icon': Icon
  }
})
</script>

<style>
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
