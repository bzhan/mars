<!-- Verification Conditions, including the formula, solver and result -->
<template>
  <div class="verification-condition">
    <div>{{vc_success_num + "/" + vc_num}}</div>
    <ul>
        <li v-for="vc_info in vc_infos" :key="vc_info.index">
        <!-- TODO: change the key -->
            <ul class="vc-formula" @mouseover="showOrigin(vc_info.origin)" @mouseleave="hideOrigin">
              <li>assume: 
                <ul>
                  <li v-for="(asm, index) in vc_info.assume" :key="index">
                  {{ asm }}
                </li>
                </ul>
              </li>
              <li>show: {{ vc_info.show }}</li>
            </ul> 
            <!-- vc_info.solver is also changed by using v-model -->
            <select v-model="vc_info.solver" @change="changeSolver(vc_info.index, vc_info.solver)" class="vc-button">
                <option value="z3">Z3</option>
                <option value="wolfram">Wolfram Engine</option>
            </select>

            <span class="vc-icon">
                <v-icon name="check-circle" style="fill:green" v-show="vc_info.result === true" scale="1.5"></v-icon>
                <v-icon name="times-circle" style="fill:red" v-show="vc_info.result === false" scale="1.5"></v-icon>
            </span>

        </li>
    </ul>
  </div>
</template>

<script>
import 'vue-awesome/icons'
import Icon from 'vue-awesome/components/Icon'
import { EditorView } from '@codemirror/view'
import { showOrigin, hideOrigin } from '../decoration/origin'
import { serverConnection } from '../serverConnection'

export default ({
    props: {
        editorView: EditorView,
        socket: WebSocket
    },

    data() {
      return{
        vc_infos: []
      }
    },

    computed: {
      vc_num() {
        return this.vc_infos.length
      },
      vc_success_num() {
        let n = 0
        for (let vc_info of this.vc_infos) {
          if (vc_info.result === true){
            n++;
          }
        }

        return n
      }
    },

  methods: {
    changeSolver(index, solver) {
      // The label of the verification condition of which solver is changed.
      let label = this.vc_infos[index].label 

      let pms_start_pos = this.vc_infos[index].pms_start_pos
      let pms_end_pos = this.vc_infos[index].pms_end_pos
      let old_proof_methods = this.editorView.state.sliceDoc(pms_start_pos+2, pms_end_pos-2)
      console.log("old_proof_methods:", old_proof_methods)

      // Transfer the proof method string into a dictionary.
      let pm_dict = this.to_proof_method_dict(old_proof_methods)
      
      // Set the value on label as solver
      pm_dict.set(label, solver)
      console.log("pm_dict:", pm_dict)

      let new_proof_methods = this.to_proof_method_string(pm_dict)

      // Change the document in the editor into new_proof_methods
      this.editorView.dispatch(this.editorView.state.update({
        changes: {from: pms_start_pos, to: pms_end_pos, insert: "{{" + new_proof_methods + "}}"}}))

      // The proof method start position and end position of each verification condition
      // may be changed after inserting.
      // Therefore call the compute() function to get the new position.
      // TODO: is there a better solution?
      this.compute()
    },

    to_proof_method_dict(pms)
    /* Transfer a proof method string into a Map object.
       Example: transfer "init: z3, maintain: wolfram" 
                into Map([[init, z3], [maintain, wolfram]])
       Note that if the proof method is "z3", without label, 
       the key for it would be set as "None" in the Map object.  **/    
    {
      console.assert(typeof(pms) === "string", "The parameter should be a string")
      pms = pms.trim()
      let pm_dict = new Map()

      if (pms === ""){
        return pm_dict
      }

      else{
        // pm_list is, for example ["init: z3", "maintain: wolfram"]
        let pm_list = pms.split(",")

        console.log("pm_list:", pm_list)

        for (let pm of pm_list){
          let key, value
          // Case when pm is with a label, set the key as label
          if (pm.includes(":")){
            key = pm.split(":")[0].trim()
            value = pm.split(":")[1].trim()
          }
          // Case when pm is without a label, set the key as None
          else{
            key = "None"
            value = pm.trim()
          }
          pm_dict.set(key, value)
        }

        return pm_dict
      }
    },

    to_proof_method_string(pm_dict)
    /* Transfer a proof method Map object into a string.
       Example: transfer Map([[init, z3], [maintain, wolfram]])
                into "init: z3, maintain: wolfram"
       Note that if the key is "None" in the Map object, for example, Map([["None", "z3"],])
       the string for it would be only the method, without a label, i.e. "z3". */  
    {
      let pm_str = ""
      let i = 0
      let end_str = ", "
      for (let [key, value] of pm_dict){
        // Each "key: value" ends with ", " except the last one.
        console.log(i)
        if (i === pm_dict.size - 1){
          end_str = ""
        }
        i ++;
        
        if (key === "None"){
          pm_str += value + end_str
        }
        else{
          pm_str += key + ": " + value + end_str
        }
      }

      return pm_str
    },
    showOrigin(origin) {
      let effects = origin.map((range) => showOrigin.of(range));
      this.editorView.dispatch({effects});
    },
    hideOrigin() {
      let effects = [hideOrigin.of({})];
      this.editorView.dispatch({effects});
    },
    computed(vcs) {
      this.vc_infos = []
      for (let i in vcs){
        let vcData = vcs[i]  // vcData is object
        let label = vcData.label
        let solver = "z3"
        
        if (vcData.method){
          solver = vcData.method
        }

        this.vc_infos.push({
          index: i,
          formula: vcData.formula,
          assume: vcData.assume,
          show: vcData.show,
          label: label,
          solver: solver,  //TODO: set the solver
          result: null,
          origin: vcData.origin,
          pred_end_pos: vcData.pred_end_pos,
          pms_start_pos: vcData.pms_start_pos,
          pms_end_pos: vcData.pms_end_pos
        })
      }
    },
    verified(eventData) {
      let i = eventData.index
      let formula = eventData.formula
      let result = eventData.result
      
      if(formula ===  this.vc_infos[i].formula)
        // Variable result stores the result of formula with index i.
        // Set the result of index i as the value of variable result.
        this.vc_infos[i].result = result
      else{
          console.error("Wrong result for the verification condition:", formula)
      }
    },
    verifyVCs() {
      // Send the computed vc formula, the index i and the choosen solver to server.
      for (let i = 0; i < this.vc_infos.length; i++){
        let formula = this.vc_infos[i].formula
        let solver = this.vc_infos[i].solver
        // we need to send the code to let the server know about the function definitions
        let code = this.editorView.state.doc.toString();
        serverConnection.socket.send(JSON.stringify({index: i, formula: formula, solver: solver, code: code, type: "verify"}))
      }
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
  border-radius: 15px;
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
