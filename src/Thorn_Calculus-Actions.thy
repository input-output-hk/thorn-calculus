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

section \<open>Actions\<close>

theory "Thorn_Calculus-Actions"
  imports
    "Thorn_Calculus-Foundations"
begin

datatype io_kind =
  Sending |
  Receiving

datatype action =
  IO \<open>io_kind\<close> \<open>chan family\<close> \<open>nat\<close> \<open>val family\<close> |
  Communication (\<open>\<tau>\<close>)

abbreviation
  sending :: "chan family \<Rightarrow> nat \<Rightarrow> val family \<Rightarrow> action"
  (\<open>(_ \<triangleleft>\<^bsub>_\<^esub>/ _)\<close> [53, 0, 53] 52)
where
  "A \<triangleleft>\<^bsub>n\<^esub> X \<equiv> IO Sending A n X"

abbreviation
  receiving :: "chan family \<Rightarrow> nat \<Rightarrow> val family \<Rightarrow> action"
  (\<open>(_ \<triangleright>\<^bsub>_\<^esub>/ _)\<close> [53, 0, 53] 52)
where
  "A \<triangleright>\<^bsub>n\<^esub> X \<equiv> IO Receiving A n X"

end
