theory "Thorn_Calculus-FIFO_Transmission"
  imports
    "Thorn_Calculus-Processes"
begin

record 'a node =
  value_in_node :: 'a
  next_nodes :: chan

typedef 'a cursor = "UNIV :: 'a node channel set" morphisms cursor_to_channel cursor_from_channel ..

text \<open>
  The morally correct way to define \<^type>\<open>node\<close> and \<^type>\<open>cursor\<close> would be defining them as
  mutually recursive datatypes with \<^const>\<open>next_nodes\<close> being of type \<^typ>\<open>'a cursor\<close>. However,
  this would require \<^type>\<open>channel\<close> to be a bounded natural functor, which is impossible to
  achieve (in particular, it is impossible to define an appropriate \<open>set\<close> function for
  \<^type>\<open>channel\<close>).
\<close>

setup_lifting type_definition_cursor

instance cursor :: (type) embeddable
  by standard (meson cursor_to_channel_inject ex_inj inj_def)

lift_definition
  fifo_send :: "'a cursor \<Rightarrow> 'a::embeddable \<Rightarrow> ('a cursor \<Rightarrow> process) \<Rightarrow> process"
  is "\<lambda>a x P. \<nu> c'. (a \<triangleleft> \<lparr>value_in_node = x, next_nodes = untyped c'\<rparr> \<parallel> P c')" .

lift_definition fifo_receive :: "'a cursor \<Rightarrow> ('a::embeddable \<Rightarrow> 'a cursor \<Rightarrow> process) \<Rightarrow> process"
  is "\<lambda>a P. a \<triangleright> (n :: 'a node). (a \<triangleleft> n \<parallel> P (value_in_node n) (typed (next_nodes n)))" .

syntax
  "_fifo_send" :: "'a cursor \<Rightarrow> pttrn \<Rightarrow> 'a::embeddable \<Rightarrow> process \<Rightarrow> process"
  (\<open>(_ \<rightarrow> _ \<triangleleft>\<^bsub>f\<^esub> _;/ _)\<close> [53, 0, 0, 52] 52)
translations
  "c \<rightarrow> c' \<triangleleft>\<^bsub>f\<^esub> x; p" \<rightleftharpoons> "CONST fifo_send c x (\<lambda>c'. p)"
print_translation \<open>
  [preserve_binder_abs_receive_tr' @{const_syntax fifo_send} @{syntax_const "_fifo_send"}]
\<close>

syntax
  "_fifo_receive" :: "'a::embeddable cursor \<Rightarrow> pttrn \<Rightarrow> pttrn \<Rightarrow> process \<Rightarrow> process"
  (\<open>(3_ \<rightarrow> _ \<triangleright>\<^bsub>f\<^esub> _./ _)\<close> [53, 0, 0, 52] 52)
translations
  "c \<rightarrow> c' \<triangleright>\<^bsub>f\<^esub> x. p" \<rightleftharpoons> "CONST fifo_receive c (\<lambda>x c'. p)"
print_translation \<open>
  [preserve_binder_abs_receive_tr' @{const_syntax fifo_receive} @{syntax_const "_fifo_receive"}]
\<close>

end
