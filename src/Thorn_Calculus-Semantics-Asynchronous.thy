(*
  Copyright 2021–2024 Input Output Global Inc.

  Licensed under the Apache License, Version 2.0 (the “License”); you may not use this file except
  in compliance with the License. You may obtain a copy of the License at

      http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software distributed under the License
  is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
  or implied. See the License for the specific language governing permissions and limitations under
  the License.
*)

section \<open>Asynchronous Semantics\<close>

theory "Thorn_Calculus-Semantics-Asynchronous"
  imports
    "Thorn_Calculus-Semantics-Synchronous"
begin

fun asynchronous_transition :: "action \<Rightarrow> process family relation" (\<open>'(\<rightarrow>\<^sub>a\<lparr>_\<rparr>')\<close>) where
  "(\<rightarrow>\<^sub>a\<lparr>A \<triangleright>\<^bsub>n\<^esub> X\<rparr>) = {\<hole> \<guillemotleft> suffix n} OO {A \<guillemotleft> suffix n \<triangleleft> X \<parallel> \<hole>}" |
  "(\<rightarrow>\<^sub>a\<lparr>\<alpha>\<rparr>) = (\<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr>)"

abbreviation
  asynchronous_transition_std :: "process family \<Rightarrow> action \<Rightarrow> process family \<Rightarrow> bool"
  (\<open>(_ \<rightarrow>\<^sub>a\<lparr>_\<rparr>/ _)\<close> [51, 0, 51] 50)
where
  "P \<rightarrow>\<^sub>a\<lparr>\<alpha>\<rparr> Q \<equiv> (\<rightarrow>\<^sub>a\<lparr>\<alpha>\<rparr>) P Q"

end
