theory BigStepTask
  imports BigStepSimple
begin

subsection \<open>Start of testing for task\<close>

type_synonym tid = real

datatype status =
  WAIT | READY | RUNNING

datatype entered =
  ezero | eone

datatype task_st =
  Sch (pool: "(real \<times> tid) list") (run_now: tid) (run_prior: real)
| Task (status: status) (entered: entered) (task_prior: real)
| None


end