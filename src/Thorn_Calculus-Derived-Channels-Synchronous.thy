text \<open>
  The technique used here is by Honda and Tokoro. See Example~1.6.2 in the \<open>\<pi>\<close>-dist thesis by
  Vyšniauskas and the paper \<^emph>\<open>An Object Calculus for Asynchronous Communication\<close> by Honda and Tokoro
  (where this technique is sort of buried in the description of a technique for sending \<^emph>\<open>sequences\<close>
  of values).
\<close>

theory "Thorn_Calculus-Derived-Channels-Synchronous"
  imports
    "Thorn_Calculus-Processes"
begin

consts
  sync_send :: "'c \<Rightarrow> 'v \<Rightarrow> 'p \<Rightarrow> 'p" (\<open>(_ \<triangleleft>\<^bsub>s\<^esub> _;/ _)\<close> [53, 0, 52] 52)
  sync_receive :: "'c \<Rightarrow> ('v \<Rightarrow> 'p) \<Rightarrow> 'p"

typedef 'a sync_channel = "UNIV :: 'a channel channel set"
  morphisms sync_channel_to_nested_channel sync_channel_from_nested_channel ..

instance sync_channel :: (type) embeddable
  by standard (meson sync_channel_to_nested_channel_inject ex_inj inj_def)

syntax
  "_sync_receive" :: "'a::embeddable sync_channel \<Rightarrow> pttrn \<Rightarrow> process \<Rightarrow> process"
  (\<open>(3_ \<triangleright>\<^bsub>s\<^esub> _./ _)\<close> [53, 0, 52] 52)
translations
  "a \<triangleright>\<^bsub>s\<^esub> x. p" \<rightleftharpoons> "CONST sync_receive a (\<lambda>x. p)"
print_translation \<open>
  [preserve_binder_abs_receive_tr' @{const_syntax sync_receive} @{syntax_const "_sync_receive"}]
\<close>

overloading
  plain_sync_send \<equiv> "sync_send :: chan \<Rightarrow> val \<Rightarrow> process \<Rightarrow> process"
  plain_sync_receive \<equiv> "receive :: chan \<Rightarrow> (val \<Rightarrow> process) \<Rightarrow> process"
begin

lift_definition plain_sync_send :: "'a sync_channel \<Rightarrow> 'a \<Rightarrow> process \<Rightarrow> process"
  is "\<lambda>A x p. A \<triangleright> (a :: 'a channel). (a \<triangleleft> x \<parallel> p)" .

lift_definition plain_sync_receive :: "'a sync_channel \<Rightarrow> ('a \<Rightarrow> process) \<Rightarrow> process"
  is "\<lambda>A P. \<nu> (a :: 'a channel). (A \<triangleleft> a \<parallel> a \<triangleright> x. P x)" .

end

overloading
  sync_send_family \<equiv> "sync_send :: chan family \<Rightarrow> val family \<Rightarrow> process family \<Rightarrow> process family"
  sync_receive_family \<equiv> "sync_receive :: chan family \<Rightarrow> (val \<Rightarrow> process family) \<Rightarrow> process family"
begin

definition sync_send_family :: "chan family \<Rightarrow> val family \<Rightarrow> process family \<Rightarrow> process family" where
  [simp]: "sync_send_family A X P = (\<lambda>e. A e \<triangleleft>\<^bsub>s\<^esub> X e; P e)"

definition sync_receive_family :: "chan family \<Rightarrow> (val \<Rightarrow> process family) \<Rightarrow> process family" where
  [simp]: "sync_receive_family A \<P> = (\<lambda>e. A e \<triangleright>\<^bsub>s\<^esub> x. \<P> x e)"

end

typedef sync_chan = "UNIV :: chan set" morphisms sync_chan_to_chan sync_chan_from_chan ..

instance sync_chan :: embeddable
  by standard (meson sync_chan_to_chan_inject ex_inj inj_def)

definition sync_untyped :: "'a sync_channel \<Rightarrow> sync_chan" where
  [simp]: "sync_untyped = sync_chan_from_chan \<circ> untyped \<circ> sync_channel_to_nested_channel"

definition sync_typed :: "sync_chan \<Rightarrow> 'a sync_channel" where
  [simp]: "sync_typed = sync_channel_from_nested_channel \<circ> typed \<circ> sync_chan_to_chan"

end
