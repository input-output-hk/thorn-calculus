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

theory "Thorn_Calculus-Core_Bisimilarities"
  imports
    "Thorn_Calculus-Semantics-Synchronous"
begin

named_theorems thorn_simps
(*FIXME: Don't name this \<^theory_text>\<open>thorn_simps\<close>, as \<^theory_text>\<open>simps\<close> alsways stands for equalities. *)

lemma receive_scope_extension [thorn_simps]:
  fixes A :: "chan family" and \<P> :: "val \<Rightarrow> chan \<Rightarrow> process family"
  shows "A \<triangleright> x. \<nu> b. \<P> x b \<sim>\<^sub>s \<nu> b. A \<triangleright> x. \<P> x b"
proof (coinduction rule: synchronous.up_to_rule [where \<F> = "[\<sim>\<^sub>s]"])
  case (forward_simulation \<alpha> S)
  then show ?case
  proof cases
    case (receiving n X)
    have "
      A \<guillemotleft> tail \<triangleright> x. \<nabla> (\<P> x)
      \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<triangleright>\<^bsub>n\<^esub> X \<guillemotleft> remove n\<rparr>
      post_receive n (X \<guillemotleft> remove n) (\<lambda>x. \<nabla> (\<P> x))"
      using synchronous_transition.receiving .
    moreover
    have "A \<guillemotleft> tail \<triangleright> x. \<nabla> (\<P> x) = \<nabla> (\<lambda>b. A \<triangleright> x. \<P> x b)"
      unfolding tail_def
      by transfer simp
    moreover
    have "post_receive n (X \<guillemotleft> remove n) (\<lambda>x. \<nabla> (\<P> x)) = \<nabla>\<^bsub>n\<^esub> (\<lambda>b. post_receive n X (\<lambda>x. \<P> x b))"
      unfolding post_receive_def
      by transfer (simp add: sdrop_shift)
    ultimately
    have "\<nu> b. A \<triangleright> x. \<P> x b \<rightarrow>\<^sub>s\<lparr>A \<triangleright>\<^bsub>n\<^esub> X\<rparr> \<nu> b. post_receive n X (\<lambda>x. \<P> x b)"
      by (simp only: new_channel_io)
    moreover
    have "\<nu> b. post_receive n X (\<lambda>x. \<P> x b) = post_receive n X (\<lambda>x. \<nu> b. \<P> x b)"
      unfolding post_receive_def
      by transfer simp
    ultimately show ?thesis
      unfolding \<open>\<alpha> = A \<triangleright>\<^bsub>n\<^esub> X\<close> and \<open>S = post_receive n X (\<lambda>x. \<nu> b. \<P> x b)\<close>
      by (intro exI conjI, use in assumption) simp
  qed
next
  case (backward_simulation \<alpha> S)
  then show ?case
  proof cases
    case scope_opening
    from scope_opening(4) show ?thesis
      by cases
  next
    case (new_channel_io \<eta> A' n X \<Q>)
    from new_channel_io(3) have "\<eta> = Receiving"
      by cases
    from new_channel_io(3) have "A' = A"
      by cases simp
    have "\<Q> = (\<lambda>b. post_receive n X (\<lambda>x. \<P> x b))"
    proof -
      from new_channel_io(3)
      have "\<nabla>\<^bsub>n\<^esub> \<Q> = post_receive n (X \<guillemotleft> remove n) (\<lambda>x. \<nabla> (\<P> x))"
        by cases
      then have "\<Delta>\<^bsub>n\<^esub> (\<nabla>\<^bsub>n\<^esub> \<Q>) = \<Delta>\<^bsub>n\<^esub> (post_receive n (X \<guillemotleft> remove n) (\<lambda>x. \<nabla> (\<P> x)))"
        by simp
      then show ?thesis
        unfolding post_receive_def
        by
          transfer
          (simp
            del: sdrop.simps(2)
            add: stake_shift sdrop_shift sdrop.simps(2) [where n = 0] stake_sdrop
          )
    qed
    have "A \<triangleright> x. \<nu> b. \<P> x b \<rightarrow>\<^sub>s\<lparr>A \<triangleright>\<^bsub>n\<^esub> X\<rparr> post_receive n X (\<lambda>x. \<nu> b. \<P> x b)"
      using receiving .
    moreover
    have "post_receive n X (\<lambda>x. \<nu> b. \<P> x b) = \<nu> b. post_receive n X (\<lambda>x. \<P> x b)"
      unfolding post_receive_def
      by transfer simp
    ultimately show ?thesis
      unfolding
        \<open>\<alpha> = IO \<eta> A' n X\<close> and \<open>\<eta> = Receiving\<close> and \<open>A' = A\<close>
      and
        \<open>S = \<nu> b. \<Q> b\<close> and \<open>\<Q> = (\<lambda>b. post_receive n X (\<lambda>x. \<P> x b))\<close>
      by (intro exI conjI, use in assumption) simp
  next
    case new_channel_communication
    from new_channel_communication(3) show ?thesis
      by cases
  qed
qed respectful

lemma tagged_receive_scope_extension [thorn_simps]:
  fixes A :: "chan family" and \<P> :: "val \<Rightarrow> chan \<Rightarrow> process family"
  shows "A \<triangleright> x. \<langle>t\<rangle> \<nu> b. \<P> x b \<sim>\<^sub>s \<langle>t\<rangle> \<nu> b. A \<triangleright> x. \<P> x b"
  unfolding tagged_new_channel_def
  using receive_scope_extension .

lemma new_channel_scope_extension [thorn_simps]:
  fixes \<P> :: "chan \<Rightarrow> chan \<Rightarrow> process family"
  shows "\<nu> a. \<nu> b. \<P> a b \<sim>\<^sub>s \<nu> b. \<nu> a. \<P> a b"
proof (coinduction arbitrary: \<P> rule: synchronous.symmetric_up_to_rule [where \<F> = "[\<sim>\<^sub>s] \<squnion> id"])
  case (simulation \<alpha> S \<P>)
  then show ?case
  proof cases
    case (scope_opening i n X A)
    from \<open>\<nu> b. \<nabla> (\<lambda>a. \<P> a b) \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<triangleleft>\<^bsub>n\<^esub> X \<guillemotleft> move n i\<rparr> S \<guillemotleft> move n i\<close> show ?thesis
    proof cases
      case (scope_opening j m)
      from scope_opening(4) have "
        \<nabla> (\<lambda>b. \<nabla> (\<lambda>a. \<P> a b)) \<guillemotleft> move 0 1
        \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<guillemotleft> tail \<guillemotleft> move 0 1 \<triangleleft>\<^bsub>m\<^esub> X \<guillemotleft> move (Suc m) i \<guillemotleft> move m j \<guillemotleft> on_suffix m (move 0 1)\<rparr>
        S \<guillemotleft> move (Suc m) i \<guillemotleft> move m j \<guillemotleft> on_suffix m (move 0 1)"
        unfolding \<open>n = Suc m\<close>
        by (fact adapted_io_transition)
      moreover
      have "\<nabla> (\<lambda>b. \<nabla> (\<lambda>a. \<P> a b)) \<guillemotleft> move 0 1 = \<nabla> (\<lambda>a. \<nabla> (\<lambda>b. \<P> a b))"
        by transfer (simp add: comp_def)
      moreover
      have "A \<guillemotleft> tail \<guillemotleft> tail \<guillemotleft> move 0 1 = A \<guillemotleft> tail \<guillemotleft> tail"
        unfolding tail_def
        by transfer (simp add: comp_def)
      moreover
      obtain i' and j'
        where
          "i' \<le> Suc m"
        and
          "j' \<le> m"
        and
          moves_rewriting: "move (Suc m) i \<bullet> move m j \<bullet> move m (Suc m) = move (Suc m) i' \<bullet> move m j'"
      proof (cases "i \<le> j")
        case True
        have "
          (move (Suc m) i \<bullet> move m j) \<bullet> move m (Suc m)
          =
          (move (Suc m) (Suc j) \<bullet> move (Suc m) i) \<bullet> move m (Suc m)"
          using \<open>j \<le> m\<close> and \<open>i \<le> j\<close>
          by (simp only: outer_move_towards_front_after_move)
        also have "\<dots> = move (Suc m) (Suc j) \<bullet> (move (Suc m) i \<bullet> move m (Suc m))"
          by (simp only: adaptation_composition_associativity)
        also have "\<dots> = move (Suc m) (Suc j) \<bullet> move m i"
          by (simp only: composition_as_move)
        finally show ?thesis
          using \<open>j \<le> m\<close> and \<open>i \<le> j\<close> and that [where i' = "Suc j" and j' = i]
          by simp
      next
        case False
        then obtain j' where "i = Suc j'" and "j \<le> j'"
          by (cases i) simp_all
        have "j' \<le> m"
          using \<open>i \<le> n\<close>
          unfolding \<open>n = Suc m\<close> and \<open>i = Suc j'\<close>
          by simp
        have "
          move (Suc m) (Suc j') \<bullet> move m j \<bullet> move m (Suc m)
          =
          move (Suc m) (Suc j') \<bullet> move m j \<bullet> move (Suc m) m"
          by (simp only: neighbor_commutation)
        also have "\<dots> = move (Suc m) (Suc j') \<bullet> (move m j \<bullet> move (Suc m) m)"
          by (simp only: adaptation_composition_associativity)
        also have "\<dots> = move (Suc m) (Suc j') \<bullet> move (Suc m) j"
          by (simp only: composition_as_move)
        also have "\<dots> = move (Suc m) j \<bullet> move m j'"
          using \<open>j' \<le> m\<close> and \<open>j \<le> j'\<close>
          by (simp only: outer_move_towards_front_after_move)
        finally show ?thesis
          using \<open>j \<le> m\<close> and \<open>j' \<le> m\<close> and that [where i' = j and j' = j']
          unfolding \<open>i = Suc j'\<close>
          by simp
      qed
      from moves_rewriting have
        "X \<guillemotleft> move (Suc m) i \<guillemotleft> move m j \<guillemotleft> on_suffix m (move 0 1) = X \<guillemotleft> move (Suc m) i' \<guillemotleft> move m j'"
      and
        "S \<guillemotleft> move (Suc m) i \<guillemotleft> move m j \<guillemotleft> on_suffix m (move 0 1) = S \<guillemotleft> move (Suc m) i' \<guillemotleft> move m j'"
        by (simp_all add: composition_adapted [symmetric] on_suffix_move)
      moreover
      have "dependent_on_chan_at i X \<longleftrightarrow> dependent_on_chan_at j' (X \<guillemotleft> move (Suc m) i')"
      proof -
        have "dependent_on_chan_at i X \<longleftrightarrow> dependent_on_chan_at (Suc m) (X \<guillemotleft> move (Suc m) i)"
          using dependent_on_chan_at_after_source_anchored_move_adapted [symmetric] .
        also have "\<dots> \<longleftrightarrow> dependent_on_chan_at (Suc m) (X \<guillemotleft> move (Suc m) i \<guillemotleft> move m j)"
          using \<open>j \<le> m\<close>
          by
            (simp
              del: dependent_on_chan_at_def
              add: dependent_on_chan_at_after_move_within_prefix_adapted
            )
        also have "\<dots> \<longleftrightarrow> dependent_on_chan_at m (X \<guillemotleft> move (Suc m) i \<guillemotleft> move m j \<guillemotleft> move m (Suc m))"
          using dependent_on_chan_at_after_source_anchored_move_adapted [symmetric] .
        also have "\<dots> \<longleftrightarrow> dependent_on_chan_at m (X \<guillemotleft> move (Suc m) i' \<guillemotleft> move m j')"
          using moves_rewriting
          by
            (simp only:
              composition_adapted [symmetric]
              adaptation_composition_associativity [symmetric]
            )
        also have "\<dots> \<longleftrightarrow> dependent_on_chan_at j' (X \<guillemotleft> move (Suc m) i')"
          using dependent_on_chan_at_after_source_anchored_move_adapted .
        finally show ?thesis .
      qed
      moreover
      have "dependent_on_chan_at j (X \<guillemotleft> move (Suc m) i) \<longleftrightarrow> dependent_on_chan_at i' X"
      proof -
        have "
          dependent_on_chan_at j (X \<guillemotleft> move (Suc m) i)
          \<longleftrightarrow>
          dependent_on_chan_at m (X \<guillemotleft> move (Suc m) i \<guillemotleft> move m j)"
          using dependent_on_chan_at_after_source_anchored_move_adapted [symmetric] .
        also have "\<dots> \<longleftrightarrow>
          dependent_on_chan_at (Suc m) (X \<guillemotleft> move (Suc m) i \<guillemotleft> move m j \<guillemotleft> move (Suc m) m)"
          using dependent_on_chan_at_after_source_anchored_move_adapted [symmetric] .
        also have "\<dots> \<longleftrightarrow>
          dependent_on_chan_at (Suc m) (X \<guillemotleft> move (Suc m) i \<guillemotleft> move m j \<guillemotleft> move m (Suc m))"
          by (simp only: neighbor_commutation)
        also have "\<dots> \<longleftrightarrow> dependent_on_chan_at (Suc m) (X \<guillemotleft> move (Suc m) i' \<guillemotleft> move m j')"
          using moves_rewriting
          by
            (simp only:
              composition_adapted [symmetric]
              adaptation_composition_associativity [symmetric]
            )
        also have "\<dots> \<longleftrightarrow> dependent_on_chan_at (Suc m) (X \<guillemotleft> move (Suc m) i')"
          using \<open>j' \<le> m\<close>
          by
            (simp
              del: dependent_on_chan_at_def
              add: dependent_on_chan_at_after_move_within_prefix_adapted
            )
        also have "\<dots> \<longleftrightarrow> dependent_on_chan_at i' X"
          using dependent_on_chan_at_after_source_anchored_move_adapted .
        finally show ?thesis .
      qed
      ultimately have "\<nu> b. \<nu> a. \<P> a b \<rightarrow>\<^sub>s\<lparr>A \<triangleleft>\<^bsub>Suc (Suc m)\<^esub> X\<rparr> S"
        using \<open>dependent_on_chan_at i X\<close> and \<open>dependent_on_chan_at j (X \<guillemotleft> move n i)\<close>
        unfolding \<open>n = Suc m\<close>
        using \<open>i' \<le> Suc m\<close> and \<open>j' \<le> m\<close>
        by (simp only: synchronous_transition.scope_opening family_uncurry_after_new_channel)
      then show ?thesis
        unfolding \<open>\<alpha> = A \<triangleleft>\<^bsub>Suc n\<^esub> X\<close> and \<open>n = Suc m\<close>
        by (intro exI conjI, assumption) simp
    next
      case (new_channel_io \<Q>)
      have "S = \<nu> b. \<Q> b \<guillemotleft> move i n"
      proof -
        have "S = S \<guillemotleft> move n i \<guillemotleft> move i n"
          by (simp only: composition_adapted [symmetric] back_and_forth_moves identity_adapted)
        also have "\<dots> = (\<nu> b. \<Q> b) \<guillemotleft> move i n"
          unfolding \<open>S \<guillemotleft> move n i = \<nu> b. \<Q> b\<close>
          using refl .
        also have "\<dots> = \<nu> b. \<Q> b \<guillemotleft> move i n"
          using adapted_after_new_channel .
        finally show ?thesis .
      qed
      have "dependent_on_chan_at i X \<longleftrightarrow> dependent_on_chan_at i (X \<guillemotleft> remove (Suc n))"
      proof -
        have "dependent_on_chan_at i X \<longleftrightarrow> dependent_on_chan_at i (X \<guillemotleft> on_suffix (Suc n) (remove 0))"
          using \<open>i \<le> n\<close>
          by (simp only: dependent_on_chan_at_after_on_suffix_adapted)
        also have "\<dots> \<longleftrightarrow> dependent_on_chan_at i (X \<guillemotleft> remove (Suc n))"
          by (simp add: on_suffix_remove)
        finally show ?thesis .
      qed
      moreover
      from new_channel_io(2)
      have "
        \<nabla> (\<lambda>b. \<nabla> (\<lambda>a. \<P> a b)) \<guillemotleft> move 0 1
        \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<guillemotleft> tail \<guillemotleft> move 0 1 \<triangleleft>\<^bsub>n\<^esub> X \<guillemotleft> move n i \<guillemotleft> remove n \<guillemotleft> on_suffix n (move 0 1)\<rparr>
        \<nabla>\<^bsub>n\<^esub> \<Q> \<guillemotleft> on_suffix n (move 0 1)"
        by (fact adapted_io_transition)
      moreover
      have "\<nabla> (\<lambda>b. \<nabla> (\<lambda>a. \<P> a b)) \<guillemotleft> move 0 1 = \<nabla> (\<lambda>a. \<nabla> (\<lambda>b. \<P> a b))"
        by transfer (simp add: comp_def)
      moreover
      have "A \<guillemotleft> tail \<guillemotleft> tail \<guillemotleft> move 0 1 = A \<guillemotleft> tail \<guillemotleft> tail"
        unfolding tail_def
        by transfer (simp add: comp_def)
      moreover
      have "X \<guillemotleft> move n i \<guillemotleft> remove n \<guillemotleft> on_suffix n (move 0 1) = X \<guillemotleft> remove (Suc n) \<guillemotleft> move n i"
      proof -
        have "
          X \<guillemotleft> move n i \<guillemotleft> remove n \<guillemotleft> on_suffix n (move 0 1)
          =
          X \<guillemotleft> move n i \<guillemotleft> remove n \<guillemotleft> move (Suc n) n"
          by (simp add: on_suffix_move neighbor_commutation)
        also have "\<dots> = X \<guillemotleft> move n i \<guillemotleft> remove (Suc n)"
          by
            (simp only:
              composition_adapted [symmetric]
              adaptation_composition_associativity
              remove_after_move
            )
        also have "\<dots> = X \<guillemotleft> remove (Suc n) \<guillemotleft> move n i"
          using \<open>i \<le> n\<close>
          by (simp only: composition_adapted [symmetric] move_after_backyard_remove)
        finally show ?thesis .
      qed
      moreover
      have "\<nabla>\<^bsub>n\<^esub> \<Q> \<guillemotleft> on_suffix n (move 0 1) = \<nabla>\<^bsub>Suc n\<^esub> (\<lambda>b. \<Q> b \<guillemotleft> move i n) \<guillemotleft> move n i"
      proof -
        have "\<nabla>\<^bsub>n\<^esub> \<Q> \<guillemotleft> on_suffix n (move 0 1) = \<nabla>\<^bsub>n\<^esub> \<Q> \<guillemotleft> move (Suc n) n"
          by (simp add: on_suffix_move neighbor_commutation)
        also have "\<dots> = \<nabla>\<^bsub>Suc n\<^esub> \<Q>"
          by (simp only: move_adapted_after_source_uncurry)
        also have "\<dots> = \<nabla>\<^bsub>Suc n\<^esub> (\<lambda>b. \<Q> b \<guillemotleft> move i n \<guillemotleft> move n i)"
          by (simp only: composition_adapted [symmetric] back_and_forth_moves identity_adapted)
        also have "\<dots> = \<nabla>\<^bsub>Suc n\<^esub> (\<lambda>b. \<Q> b \<guillemotleft> move i n) \<guillemotleft> move n i"
          using \<open>i \<le> n\<close>
          by (simp only: move_adapted_after_deeper_uncurry)
        finally show ?thesis .
      qed
      ultimately have "\<nu> b. \<nu> a. \<P> a b \<rightarrow>\<^sub>s\<lparr>A \<triangleleft>\<^bsub>Suc n\<^esub> X\<rparr> \<nu> b. \<Q> b \<guillemotleft> move i n"
        using \<open>i \<le> n\<close> and \<open>dependent_on_chan_at i X\<close>
        by
          (simp only:
            synchronous_transition.scope_opening
            family_uncurry_after_new_channel
            synchronous_transition.new_channel_io
          )
      then show ?thesis
        unfolding \<open>\<alpha> = A \<triangleleft>\<^bsub>Suc n\<^esub> X\<close> and \<open>S = \<nu> b. \<Q> b \<guillemotleft> move i n\<close>
        by (intro exI conjI, use in assumption) simp
    qed
  next
    case (new_channel_io \<eta> A n X \<Q>)
    from \<open>\<nu> b. \<nabla> (\<lambda>a. \<P> a b) \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> tail) n (X \<guillemotleft> remove n)\<rparr> \<nabla>\<^bsub>n\<^esub> \<Q>\<close> show ?thesis
    proof cases
      case (scope_opening i m)
      have "dependent_on_chan_at i (X \<guillemotleft> remove (Suc m)) \<longleftrightarrow> dependent_on_chan_at i X"
      proof -
        have "
          dependent_on_chan_at i (X \<guillemotleft> remove (Suc m))
          \<longleftrightarrow>
          dependent_on_chan_at i (X \<guillemotleft> on_suffix (Suc m) (remove 0))"
          by (simp add: on_suffix_remove)
        also have "\<dots> \<longleftrightarrow> dependent_on_chan_at i X"
          using \<open>i \<le> m\<close>
          by (simp only: dependent_on_chan_at_after_on_suffix_adapted)
        finally show ?thesis .
      qed
      moreover
      from scope_opening(5) have "
        \<nabla> (\<lambda>b. \<nabla> (\<lambda>a. \<P> a b)) \<guillemotleft> move 0 1
        \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<guillemotleft> tail \<guillemotleft> move 0 1 \<triangleleft>\<^bsub>m\<^esub> X \<guillemotleft> remove (Suc m) \<guillemotleft> move m i \<guillemotleft> on_suffix m (move 0 1)\<rparr>
        \<nabla>\<^bsub>Suc m\<^esub> \<Q> \<guillemotleft> move m i \<guillemotleft> on_suffix m (move 0 1)"
        unfolding \<open>n = Suc m\<close>
        by (fact adapted_io_transition)
      moreover
      have "\<nabla> (\<lambda>b. \<nabla> (\<lambda>a. \<P> a b)) \<guillemotleft> move 0 1 = \<nabla> (\<lambda>a. \<nabla> (\<lambda>b. \<P> a b))"
        by transfer (simp add: comp_def)
      moreover
      have "A \<guillemotleft> tail \<guillemotleft> tail \<guillemotleft> move 0 1 = A \<guillemotleft> tail \<guillemotleft> tail"
        unfolding tail_def
        by transfer (simp add: comp_def)
      moreover
      have "X \<guillemotleft> remove (Suc m) \<guillemotleft> move m i \<guillemotleft> on_suffix m (move 0 1) = X \<guillemotleft> move m i \<guillemotleft> remove m"
      proof -
        have "
          X \<guillemotleft> remove (Suc m) \<guillemotleft> move m i \<guillemotleft> on_suffix m (move 0 1)
          =
          X \<guillemotleft> move m i \<guillemotleft> remove (Suc m) \<guillemotleft> on_suffix m (move 0 1)"
          using \<open>i \<le> m\<close>
          by (simp only: composition_adapted [symmetric] move_after_backyard_remove)
        also have "\<dots> = X \<guillemotleft> move m i \<guillemotleft> remove (Suc m) \<guillemotleft> move m (Suc m)"
          by (simp add: on_suffix_move)
        also have "\<dots> = X \<guillemotleft> move m i \<guillemotleft> remove m"
          by
            (simp only:
              composition_adapted [symmetric]
              adaptation_composition_associativity
              remove_after_move
            )
        finally show ?thesis .
      qed
      moreover
      have "\<nabla>\<^bsub>Suc m\<^esub> \<Q> \<guillemotleft> move m i \<guillemotleft> on_suffix m (move 0 1) = \<nabla>\<^bsub>m\<^esub> (\<lambda>a. \<Q> a \<guillemotleft> move m i)"
      proof -
        have "
          \<nabla>\<^bsub>Suc m\<^esub> \<Q> \<guillemotleft> move m i \<guillemotleft> on_suffix m (move 0 1)
          =
          \<nabla>\<^bsub>Suc m\<^esub> (\<lambda>a. \<Q> a \<guillemotleft> move m i) \<guillemotleft> on_suffix m (move 0 1)"
          using \<open>i \<le> m\<close>
          by (simp only: move_adapted_after_deeper_uncurry)
        also have "\<dots> = \<nabla>\<^bsub>Suc m\<^esub> (\<lambda>a. \<Q> a \<guillemotleft> move m i) \<guillemotleft> move m (Suc m)"
          by (simp add: on_suffix_move)
        also have "\<dots> = \<nabla>\<^bsub>m\<^esub> (\<lambda>a. \<Q> a \<guillemotleft> move m i)"
          by (simp only: move_adapted_after_source_uncurry)
        finally show ?thesis .
      qed
      ultimately have "\<nu> b. \<nu> a. \<P> a b \<rightarrow>\<^sub>s\<lparr>A \<triangleleft>\<^bsub>Suc m\<^esub> X\<rparr> \<nu> a. \<Q> a"
        using \<open>i \<le> m\<close> and \<open>dependent_on_chan_at i (X \<guillemotleft> remove n)\<close>
        unfolding \<open>n = Suc m\<close>
        by
          (simp only:
            synchronous_transition.new_channel_io
            family_uncurry_after_new_channel
            adapted_after_new_channel
            synchronous_transition.scope_opening
          )
      then show ?thesis
        unfolding \<open>\<alpha> = IO \<eta> A n X\<close> and \<open>S = \<nu> a. \<Q> a\<close> and \<open>\<eta> = Sending\<close> and \<open>n = Suc m\<close>
        by (intro exI conjI, use in assumption) simp
    next
      case (new_channel_io \<R>)
      have "\<Q> = (\<lambda>a. \<nu> b. \<Delta>\<^bsub>n\<^esub> (\<R> b) a)"
      proof -
        have "\<Q> = \<Delta>\<^bsub>n\<^esub> (\<nabla>\<^bsub>n\<^esub> \<Q>)"
          by (simp only: deep_curry_after_deep_uncurry pointfree_idE)
        also have "\<dots> = \<Delta>\<^bsub>n\<^esub> (\<nu> b. \<R> b)"
          unfolding \<open>\<nabla>\<^bsub>n\<^esub> \<Q> = \<nu> b. \<R> b\<close>
          using refl .
        also have "\<dots> = (\<lambda>a. \<nu> b. \<Delta>\<^bsub>n\<^esub> (\<R> b) a)"
          by simp
        finally show ?thesis .
      qed
      from new_channel_io(2) have "
        \<nabla> (\<lambda>b. \<nabla> (\<lambda>a. \<P> a b)) \<guillemotleft> move 0 1
        \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> tail \<guillemotleft> tail \<guillemotleft> move 0 1) n (X \<guillemotleft> remove n \<guillemotleft> remove n \<guillemotleft> on_suffix n (move 0 1))\<rparr>
        \<nabla>\<^bsub>n\<^esub> \<R> \<guillemotleft> on_suffix n (move 0 1)"
        by (fact adapted_io_transition)
      moreover
      have "\<nabla> (\<lambda>b. \<nabla> (\<lambda>a. \<P> a b)) \<guillemotleft> move 0 1 = \<nabla> (\<lambda>a. \<nabla> (\<lambda>b. \<P> a b))"
        by transfer (simp add: comp_def)
      moreover
      have "A \<guillemotleft> tail \<guillemotleft> tail \<guillemotleft> move 0 1 = A \<guillemotleft> tail \<guillemotleft> tail"
        unfolding tail_def
        by transfer (simp add: comp_def)
      moreover
      have "X \<guillemotleft> remove n \<guillemotleft> remove n \<guillemotleft> on_suffix n (move 0 1) = X \<guillemotleft> remove n \<guillemotleft> remove n"
      proof -
        have "
          X \<guillemotleft> remove n \<guillemotleft> remove n \<guillemotleft> on_suffix n (move 0 1)
          =
          X \<guillemotleft> remove n \<guillemotleft> remove n \<guillemotleft> move (Suc n) n"
          by (simp add: on_suffix_move neighbor_commutation)
        also have "\<dots> = X \<guillemotleft> remove n \<guillemotleft> remove (Suc n)"
          by
            (simp only:
              composition_adapted [symmetric]
              adaptation_composition_associativity
              remove_after_move
            )
        also have "\<dots> = X \<guillemotleft> remove n \<guillemotleft> remove n"
          by
            transfer
            (simp
              del: stake.simps(2) sdrop.simps(2)
              add: comp_def stake_shift sdrop_shift take_stake min_absorb1
            )
        finally show ?thesis .
      qed
      moreover
      have "\<nabla>\<^bsub>n\<^esub> \<R> \<guillemotleft> on_suffix n (move 0 1) = \<nabla>\<^bsub>n\<^esub> (\<lambda>a. \<nabla>\<^bsub>n\<^esub> (\<lambda>b. \<Delta>\<^bsub>n\<^esub> (\<R> b) a))"
      proof -
        have "\<nabla>\<^bsub>n\<^esub> \<R> \<guillemotleft> on_suffix n (move 0 1) = \<nabla>\<^bsub>n\<^esub> \<R> \<guillemotleft> move (Suc n) n"
          by (simp add: on_suffix_move neighbor_commutation)
        also have "\<dots> = \<nabla>\<^bsub>Suc n\<^esub> \<R>"
          by (simp only: move_adapted_after_source_uncurry)
        also have "\<dots> = \<nabla>\<^bsub>Suc n\<^esub> (\<lambda>b. \<nabla>\<^bsub>n\<^esub> (\<Delta>\<^bsub>n\<^esub> (\<R> b)))"
          by (simp only: deep_uncurry_after_deep_curry pointfree_idE)
        also have "\<dots> = \<nabla>\<^bsub>n\<^esub> (\<lambda>a. \<nabla>\<^bsub>n\<^esub> (\<lambda>b. \<Delta>\<^bsub>n\<^esub> (\<R> b) a))"
          by (simp only: deep_uncurry_reordering)
        finally show ?thesis .
      qed
      ultimately have "\<nu> b. \<nu> a. \<P> a b \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> \<nu> b. \<nu> a. \<Delta>\<^bsub>n\<^esub> (\<R> b) a"
        by
          (simp only:
            synchronous_transition.new_channel_io
            family_uncurry_after_new_channel
            deep_uncurry_after_new_channel
          )
      then show ?thesis
        unfolding \<open>\<alpha> = IO \<eta> A n X\<close> and \<open>S = \<nu> a. \<Q> a\<close> and \<open>\<Q> = (\<lambda>a. \<nu> b. \<Delta>\<^bsub>n\<^esub> (\<R> b) a)\<close>
        by (intro exI conjI, use in assumption) auto
    qed
  next
    case (new_channel_communication \<Q>)
    from \<open>\<nu> b. \<nabla> (\<lambda>a. \<P> a b) \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<nabla> \<Q>\<close> show ?thesis
    proof cases
      case (new_channel_communication \<R>)
      have "\<Q> = (\<lambda>a. \<nu> b. \<Delta> (\<R> b) a)"
      proof -
        have "\<Q> = \<Delta> (\<nabla> \<Q>)"
          by simp
        also have "\<dots> = \<Delta> (\<nu> b. \<R> b)"
          unfolding \<open>\<nabla> \<Q> = \<nu> b. \<R> b\<close>
          using refl .
        also have "\<dots> = (\<lambda>a. \<nu> b. \<Delta> (\<R> b) a)"
          by simp
        finally show ?thesis .
      qed
      from new_channel_communication(2)
      have "\<nabla> (\<lambda>b. \<nabla> (\<lambda>a. \<P> a b)) \<guillemotleft> move 0 1 \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<nabla> \<R> \<guillemotleft> move 0 1"
        by (fact adapted_communication_transition)
      moreover
      have "\<nabla> (\<lambda>b. \<nabla> (\<lambda>a. \<P> a b)) \<guillemotleft> move 0 1 = \<nabla> (\<lambda>a. \<nabla> (\<lambda>b. \<P> a b))"
        by transfer (simp add: comp_def)
      moreover
      have "\<nabla> \<R> \<guillemotleft> move 0 1 = \<nabla> (\<lambda>a. \<nabla> (\<lambda>b. \<Delta> (\<R> b) a))"
        by transfer (simp add: comp_def)
      ultimately have "\<nu> b. \<nu> a. \<P> a b \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<nu> b. \<nu> a. \<Delta> (\<R> b) a"
        by
          (simp only:
            synchronous_transition.new_channel_communication
            family_uncurry_after_new_channel
          )
      then show ?thesis
        unfolding \<open>\<alpha> = \<tau>\<close> and \<open>S = \<nu> a. \<Q> a\<close> and \<open>\<Q> = (\<lambda>a. \<nu> b. \<Delta> (\<R> b) a)\<close>
        by (intro exI conjI, use in assumption) auto
    qed
  qed
qed (respectful, iprover)

lemma guarded_tagged_new_channel_scope_extension [thorn_simps]:
  assumes "t < s"
  shows "\<langle>t\<rangle> \<nu> a. \<langle>s\<rangle> \<nu> b. \<P> a b \<sim>\<^sub>s \<langle>s\<rangle> \<nu> b. \<langle>t\<rangle> \<nu> a. \<P> a b"
  unfolding tagged_new_channel_def
  using new_channel_scope_extension .

context begin

private lemma create_channel_power_after_neighbor_commutation_adapted:
  assumes "Suc i < n"
  shows "\<star>\<^bsup>n\<^esup> (P \<guillemotleft> move i (Suc i)) \<sim>\<^sub>s \<star>\<^bsup>n\<^esup> P"
proof -
  have "\<star> (\<star> (\<star>\<^bsup>i\<^esup> (P \<guillemotleft> move i (Suc i)))) = \<star> (\<star> (\<star>\<^bsup>i\<^esup> (P \<guillemotleft> on_suffix i (move 0 1))))"
    by (simp add: on_suffix_move)
  also have "\<dots> = \<star> (\<star> (\<star>\<^bsup>i\<^esup> P \<guillemotleft> move 0 1))"
    by (simp only: adapted_after_create_channel_power)
  also have "\<dots> \<sim>\<^sub>s \<star> (\<star> (\<star>\<^bsup>i\<^esup> P))"
    using new_channel_scope_extension
    by transfer simp
  finally have "\<star>\<^bsup>Suc (Suc i)\<^esup> (P \<guillemotleft> move i (Suc i)) \<sim>\<^sub>s \<star>\<^bsup>Suc (Suc i)\<^esup> P"
    by simp
  with \<open>Suc i < n\<close> show ?thesis
    by
      (auto
        dest:
          synchronous.create_channel_power_is_compatible_with_bisimilarity
            [where n = "n - Suc (Suc i)"]
        simp only:
          funpow_add [symmetric, THEN fun_cong, unfolded comp_def]
          Suc_leI
          le_add_diff_inverse
          add.commute
      )
qed

private lemma create_channel_power_after_move_away_from_front_adapted:
  assumes "i \<le> j" and "j < n"
  shows "\<star>\<^bsup>n\<^esup> (P \<guillemotleft> move i j) \<sim>\<^sub>s \<star>\<^bsup>n\<^esup> P"
using \<open>i \<le> j\<close> proof (induction rule: inc_induct)
  case base
  then show ?case
    by (simp add: identity_as_move [symmetric] identity_adapted)
next
  case (step k)
  have "\<star>\<^bsup>n\<^esup> (P \<guillemotleft> move k j) = \<star>\<^bsup>n\<^esup> (P \<guillemotleft> move (Suc k) j \<guillemotleft> move k (Suc k))"
    by (simp only: composition_adapted [symmetric] composition_as_move)
  also have "\<dots> \<sim>\<^sub>s \<star>\<^bsup>n\<^esup> (P \<guillemotleft> move (Suc k) j)"
    using \<open>k < j\<close> and \<open>j < n\<close>
    by (simp only: create_channel_power_after_neighbor_commutation_adapted)
  also have "\<dots> \<sim>\<^sub>s \<star>\<^bsup>n\<^esup> P"
    using step.IH .
  finally show ?case .
qed

lemma create_channel_power_after_move_adapted:
  assumes "i < n" and "j < n"
  shows "\<star>\<^bsup>n\<^esup> (P \<guillemotleft> move i j) \<sim>\<^sub>s \<star>\<^bsup>n\<^esup> P"
proof (cases "i \<le> j")
  case True
  with \<open>j < n\<close> show ?thesis
    by (intro create_channel_power_after_move_away_from_front_adapted)
next
  case False
  have "\<star>\<^bsup>n\<^esup> (P \<guillemotleft> move i j) \<sim>\<^sub>s \<star>\<^bsup>n\<^esup> (P \<guillemotleft> move i j \<guillemotleft> move j i)"
    using \<open>i < n\<close> and \<open>\<not> i \<le> j\<close>
    by
      (simp only:
        create_channel_power_after_move_away_from_front_adapted
          [THEN synchronous.bisimilarity_symmetry_rule]
      )
  also have "\<dots> = \<star>\<^bsup>n\<^esup> P"
    by (simp only: composition_adapted [symmetric] back_and_forth_moves identity_adapted)
  finally show ?thesis .
qed

end

context begin

private lemma independent_value_adjustment:
  shows"\<star>\<^bsup>n\<^esup> (\<nu> a. (\<Delta>\<^bsub>n\<^esub> P' a \<parallel> Q')) \<sim>\<^sub>s \<star>\<^bsup>Suc n\<^esup> (P' \<parallel> Q' \<guillemotleft> remove n)"
proof -
  have "\<star>\<^bsup>n\<^esup> (\<nu> a. (\<Delta>\<^bsub>n\<^esub> P' a \<parallel> Q')) = \<star>\<^bsup>n\<^esup> (\<nu> a. (\<Delta> (P' \<guillemotleft> move 0 n) a \<parallel> Q'))"
    by (simp only: family_curry_as_deep_curry source_curry_after_move_adapted)
  also have "\<dots> = \<star>\<^bsup>Suc n\<^esup> (P' \<guillemotleft> move 0 n \<parallel> Q' \<guillemotleft> remove 0)"
    unfolding funpow_Suc_right
    by transfer simp
  also have "\<dots> = \<star>\<^bsup>Suc n\<^esup> ((P' \<parallel> Q' \<guillemotleft> remove n) \<guillemotleft> move 0 n)"
    by (simp only: adapted_after_parallel composition_adapted [symmetric] remove_after_move)
  also have "\<dots> \<sim>\<^sub>s \<star>\<^bsup>Suc n\<^esup> (P' \<parallel> Q' \<guillemotleft> remove n)"
    by (simp only: create_channel_power_after_move_adapted)
  finally show ?thesis .
qed

lemma parallel_left_scope_extension [thorn_simps]:
  fixes \<P> :: "chan \<Rightarrow> process family"
  shows "\<nu> a. \<P> a \<parallel> Q \<sim>\<^sub>s \<nu> a. (\<P> a \<parallel> Q)"
proof (coinduction arbitrary: \<P> Q rule: synchronous.up_to_rule [where \<F> = "[\<sim>\<^sub>s] \<squnion> (\<M> \<frown> [\<sim>\<^sub>s])"])
  case (forward_simulation \<alpha> S \<P> Q)
  then show ?case
  proof cases
    case (communication \<eta> \<mu> A n X R Q')
    from \<open>\<nu> a. \<P> a \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> R\<close> show ?thesis
    proof cases
      case (scope_opening i m)
      from \<open>\<eta> \<noteq> \<mu>\<close> and \<open>\<eta> = Sending\<close> have "\<mu> = Receiving"
        by (cases \<mu>) simp
      from \<open>Q \<rightarrow>\<^sub>s\<lparr>IO \<mu> A n X\<rparr> Q'\<close> and \<open>i \<le> m\<close> have "Q \<rightarrow>\<^sub>s\<lparr>A \<triangleright>\<^bsub>Suc m\<^esub> X \<guillemotleft> move m i\<rparr> Q' \<guillemotleft> move m i"
        unfolding \<open>\<mu> = Receiving\<close> and \<open>n = Suc m\<close>
        by (simp only: receiving_transition_with_move_adapted_target_part)
      then have "Q \<guillemotleft> remove 0 \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> remove 0 \<triangleright>\<^bsub>m\<^esub> X \<guillemotleft> move m i\<rparr> Q' \<guillemotleft> move m i"
        by
          (simp add:
            receiving_transition_with_remove_adapted_source_part
            identity_as_move [symmetric]
            identity_adapted
          )
      then have "Q \<guillemotleft> tail \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<triangleright>\<^bsub>m\<^esub> X \<guillemotleft> move m i\<rparr> Q' \<guillemotleft> move m i"
        unfolding tail_def
        by transfer (simp add: comp_def)
      with \<open>\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<triangleleft>\<^bsub>m\<^esub> X \<guillemotleft> move m i\<rparr> R \<guillemotleft> move m i\<close>
      have "\<nabla> \<P> \<parallel> Q \<guillemotleft> tail \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<star>\<^bsup>m\<^esup> (R \<guillemotleft> move m i \<parallel> Q' \<guillemotleft> move m i)"
        by (blast intro: synchronous_transition.communication)
      then have "\<nabla> (\<lambda>a. \<P> a \<parallel> Q) \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<star>\<^bsup>m\<^esup> ((R \<parallel> Q') \<guillemotleft> move m i)"
        unfolding tail_def and adapted_after_parallel
        by transfer simp
      then have "\<nu> a. (\<P> a \<parallel> Q) \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<star>\<^bsup>Suc m\<^esup> ((R \<parallel> Q') \<guillemotleft> move m i)"
        unfolding funpow.simps(2) and create_channel_def and comp_def
        by (intro new_channel_communication) simp
      moreover
      from \<open>i \<le> m\<close> have "\<star>\<^bsup>Suc m\<^esup> (R \<parallel> Q') \<sim>\<^sub>s \<star>\<^bsup>Suc m\<^esup> ((R \<parallel> Q') \<guillemotleft> move m i)"
        by
          (simp only:
            create_channel_power_after_move_adapted [THEN synchronous.bisimilarity_symmetry_rule]
          )
      ultimately show ?thesis
        unfolding \<open>\<alpha> = \<tau>\<close> and \<open>S = \<star>\<^bsup>n\<^esup> (R \<parallel> Q')\<close> and \<open>n = Suc m\<close>
        by (intro exI conjI, use in assumption) simp
    next
      case (new_channel_io \<P>')
      from \<open>Q \<rightarrow>\<^sub>s\<lparr>IO \<mu> A n X\<rparr> Q'\<close>
      have "Q \<guillemotleft> remove 0 \<rightarrow>\<^sub>s\<lparr>IO \<mu> (A \<guillemotleft> remove 0) n (X \<guillemotleft> remove n)\<rparr> Q' \<guillemotleft> remove n"
        using adapted_io_transition [where \<E> = "remove 0"]
        by (simp add: on_suffix_remove)
      then have "Q \<guillemotleft> tail \<rightarrow>\<^sub>s\<lparr>IO \<mu> (A \<guillemotleft> tail) n (X \<guillemotleft> remove n)\<rparr> Q' \<guillemotleft> remove n"
        unfolding tail_def
        by transfer (simp add: comp_def)
      with \<open>\<eta> \<noteq> \<mu>\<close> and \<open>\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> tail) n (X \<guillemotleft> remove n)\<rparr> \<nabla>\<^bsub>n\<^esub> \<P>'\<close>
      have "\<nabla> \<P> \<parallel> Q \<guillemotleft> tail \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<star>\<^bsup>n\<^esup> (\<nabla>\<^bsub>n\<^esub> \<P>' \<parallel> Q' \<guillemotleft> remove n)"
        by (fact synchronous_transition.communication)
      then have "\<nabla> (\<lambda>a. \<P> a \<parallel> Q) \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<star>\<^bsup>n\<^esup> (\<nabla>\<^bsub>n\<^esub> (\<lambda>a. \<P>' a \<parallel> Q'))"
        unfolding tail_def
        by transfer simp
      then have "\<nu> a. (\<P> a \<parallel> Q) \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<star>\<^bsup>Suc n\<^esup> (\<nabla>\<^bsub>n\<^esub> (\<lambda>a. \<P>' a \<parallel> Q'))"
        unfolding funpow.simps(2) and create_channel_def and comp_def
        by (intro new_channel_communication) simp
      moreover
      have "\<star>\<^bsup>n\<^esup> (\<nu> a. (\<P>' a \<parallel> Q')) \<sim>\<^sub>s \<star>\<^bsup>Suc n\<^esup> (\<nabla>\<^bsub>n\<^esub> (\<lambda>a. \<P>' a \<parallel> Q'))"
      proof -
        have "\<star>\<^bsup>n\<^esup> (\<nu> a. (\<P>' a \<parallel> Q')) = \<star>\<^bsup>Suc n\<^esup> (\<nabla> (\<lambda>a. \<P>' a \<parallel> Q'))"
          unfolding funpow_Suc_right
          by simp
        also have "\<dots> \<sim>\<^sub>s \<star>\<^bsup>Suc n\<^esup> (\<nabla> (\<lambda>a. \<P>' a \<parallel> Q') \<guillemotleft> move n 0)"
          by (simp only: create_channel_power_after_move_adapted [symmetric])
        also have "\<dots> = \<star>\<^bsup>Suc n\<^esup> (\<nabla>\<^bsub>n\<^esub> (\<lambda>a. \<P>' a \<parallel> Q'))"
          by (simp only: family_uncurry_as_deep_uncurry move_adapted_after_source_uncurry)
        finally show ?thesis .
      qed
      ultimately show ?thesis
        unfolding \<open>\<alpha> = \<tau>\<close> and \<open>S = \<star>\<^bsup>n\<^esup> (R \<parallel> Q')\<close> and \<open>R = \<nu> a. \<P>' a\<close>
        using power_in_universe [OF create_channel_mutation_in_universe]
        by (intro exI conjI, use in assumption) force
    qed
  next
    case (parallel_left_io \<eta> A n X R)
    from \<open>\<nu> a. \<P> a \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> R\<close> show ?thesis
    proof cases
      case (scope_opening i m)
      from \<open>\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<triangleleft>\<^bsub>m\<^esub> X \<guillemotleft> move m i\<rparr> R \<guillemotleft> move m i\<close>
      have "\<nabla> \<P> \<parallel> Q \<guillemotleft> tail \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<triangleleft>\<^bsub>m\<^esub> X \<guillemotleft> move m i\<rparr> R \<guillemotleft> move m i \<parallel> Q \<guillemotleft> tail \<guillemotleft> suffix m"
        by (fact synchronous_transition.parallel_left_io)
      with \<open>i \<le> m\<close>
      have "\<nabla> (\<lambda>a. \<P> a \<parallel> Q) \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<triangleleft>\<^bsub>m\<^esub> X \<guillemotleft> move m i\<rparr> (R \<parallel> Q \<guillemotleft> suffix (Suc m)) \<guillemotleft> move m i"
        unfolding tail_def
        by
          (simp only: adapted_after_parallel composition_adapted [symmetric] suffix_after_move)
          (transfer, simp)
      with \<open>i \<le> m\<close> and \<open>dependent_on_chan_at i X\<close>
      have "\<nu> a. (\<P> a \<parallel> Q) \<rightarrow>\<^sub>s\<lparr>A \<triangleleft>\<^bsub>Suc m\<^esub> X\<rparr> R \<parallel> Q \<guillemotleft> suffix (Suc m)"
        by (fact synchronous_transition.scope_opening)
      then show ?thesis
        unfolding \<open>\<alpha> = IO \<eta> A n X\<close> and \<open>S = R \<parallel> Q \<guillemotleft> suffix n\<close> and \<open>\<eta> = Sending\<close> and \<open>n = Suc m\<close>
        by (intro exI conjI, use in assumption) simp
    next
      case (new_channel_io \<P>')
      from \<open>\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> tail) n (X \<guillemotleft> remove n)\<rparr> \<nabla>\<^bsub>n\<^esub> \<P>'\<close>
      have "\<nabla> \<P> \<parallel> Q \<guillemotleft> tail \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> tail) n (X \<guillemotleft> remove n)\<rparr> \<nabla>\<^bsub>n\<^esub> \<P>' \<parallel> Q \<guillemotleft> tail \<guillemotleft> suffix n"
        by (fact synchronous_transition.parallel_left_io)
      then have "\<nabla> (\<lambda>a. \<P> a \<parallel> Q) \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> tail) n (X \<guillemotleft> remove n)\<rparr> \<nabla>\<^bsub>n\<^esub> (\<lambda>a. \<P>' a \<parallel> Q \<guillemotleft> suffix n)"
        unfolding tail_def
        by transfer (simp add: sdrop_shift)
      then have "\<nu> a. (\<P> a \<parallel> Q) \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> \<nu> a. (\<P>' a \<parallel> Q \<guillemotleft> suffix n)"
        by (fact synchronous_transition.new_channel_io)
      then show ?thesis
        unfolding \<open>\<alpha> = IO \<eta> A n X\<close> and \<open>S = R \<parallel> Q \<guillemotleft> suffix n\<close> and \<open>R = \<nu> a. \<P>' a\<close>
        using equality_in_universe
        by (intro exI conjI, use in assumption) force
    qed
  next
    case (parallel_left_communication R)
    from \<open>\<nu> a. \<P> a \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> R\<close> show ?thesis
    proof cases
      case (new_channel_communication \<P>')
      from \<open>\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<nabla> \<P>'\<close> have "\<nabla> \<P> \<parallel> Q \<guillemotleft> tail \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<nabla> \<P>' \<parallel> Q \<guillemotleft> tail"
        by (fact synchronous_transition.parallel_left_communication)
      then have "\<nabla> (\<lambda>a. \<P> a \<parallel> Q) \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<nabla> (\<lambda>a. \<P>' a \<parallel> Q)"
        unfolding tail_def
        by transfer simp
      then have "\<nu> a. (\<P> a \<parallel> Q) \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<nu> a. (\<P>' a \<parallel> Q)"
        by (fact synchronous_transition.new_channel_communication)
      then show ?thesis
        unfolding \<open>\<alpha> = \<tau>\<close> and \<open>S = R \<parallel> Q\<close> and \<open>R = \<nu> a. \<P>' a\<close>
        using equality_in_universe
        by (intro exI conjI, use in assumption) force
    qed
  next
    case (parallel_right_io \<eta> A n X Q')
    from \<open>Q \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> Q'\<close>
    have "Q \<guillemotleft> remove 0 \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> remove 0) n (X \<guillemotleft> remove n)\<rparr> Q' \<guillemotleft> remove n"
      using adapted_io_transition [where \<E> = "remove 0"]
      by (simp add: on_suffix_remove)
    then have "Q \<guillemotleft> tail \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> tail) n (X \<guillemotleft> remove n)\<rparr> Q' \<guillemotleft> remove n"
      unfolding tail_def
      by transfer (simp add: comp_def)
    then have "\<nabla> \<P> \<parallel> Q \<guillemotleft> tail \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> tail) n (X \<guillemotleft> remove n)\<rparr> \<nabla> \<P> \<guillemotleft> suffix n \<parallel> Q' \<guillemotleft> remove n"
      by (fact synchronous_transition.parallel_right_io)
    then have "\<nabla> (\<lambda>a. \<P> a \<parallel> Q) \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> tail) n (X \<guillemotleft> remove n)\<rparr> \<nabla>\<^bsub>n\<^esub> (\<lambda>a. \<P> a \<guillemotleft> suffix n \<parallel> Q')"
      unfolding tail_def
      by transfer (simp add: sdrop_shift)
    then have "\<nu> a. (\<P> a \<parallel> Q) \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> \<nu> a. (\<P> a \<guillemotleft> suffix n \<parallel> Q')"
      by (fact new_channel_io)
    then show ?thesis
      unfolding
        \<open>\<alpha> = IO \<eta> A n X\<close>
      and
        \<open>S = (\<nu> a. \<P> a) \<guillemotleft> suffix n \<parallel> Q'\<close> [unfolded adapted_after_new_channel]
      using equality_in_universe
      by (intro exI conjI, use in assumption) force
  next
    case (parallel_right_communication Q')
    from \<open>Q \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> Q'\<close> have "Q \<guillemotleft> tail \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> Q' \<guillemotleft> tail"
      by (fact adapted_communication_transition)
    then have "\<nabla> \<P> \<parallel> Q \<guillemotleft> tail \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<nabla> \<P> \<parallel> Q' \<guillemotleft> tail"
      by (fact synchronous_transition.parallel_right_communication)
    then have "\<nabla> (\<lambda>a. \<P> a \<parallel> Q) \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<nabla> (\<lambda>a. \<P> a \<parallel> Q')"
      unfolding tail_def
      by transfer simp
    then have "\<nu> a. (\<P> a \<parallel> Q) \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<nu> a. (\<P> a \<parallel> Q')"
      by (fact new_channel_communication)
    then show ?thesis
      unfolding \<open>\<alpha> = \<tau>\<close> and \<open>S = \<nu> a. \<P> a \<parallel> Q'\<close>
      using equality_in_universe
      by (intro exI conjI, use in assumption) force
  qed
next
  case (backward_simulation \<alpha> S \<P> Q)
  then show ?case
  proof cases
    case (scope_opening i n X A)
    from \<open>\<nabla> \<P> \<parallel> Q \<guillemotleft> tail \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<triangleleft>\<^bsub>n\<^esub> X \<guillemotleft> move n i\<rparr> S \<guillemotleft> move n i\<close> show ?thesis
    proof cases
      case (parallel_left_io P')
      have "S = P' \<guillemotleft> move i n \<parallel> Q \<guillemotleft> suffix (Suc n)"
      proof -
        have "S = S \<guillemotleft> move n i \<guillemotleft> move i n"
          by (simp only: composition_adapted [symmetric] back_and_forth_moves identity_adapted)
        also have "\<dots> = (P' \<parallel> Q \<guillemotleft> suffix (Suc n)) \<guillemotleft> move i n"
          unfolding \<open>S \<guillemotleft> move n i = P' \<parallel> Q \<guillemotleft> tail \<guillemotleft> suffix n\<close> and tail_def
          by transfer simp
        also have "\<dots> = P' \<guillemotleft> move i n \<parallel> Q \<guillemotleft> suffix (Suc n)"
          using \<open>i \<le> n\<close>
          by (simp only: adapted_after_parallel composition_adapted [symmetric] suffix_after_move)
        finally show ?thesis .
      qed
      from \<open>i \<le> n\<close> and \<open>dependent_on_chan_at i X\<close> and \<open>\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<triangleleft>\<^bsub>n\<^esub> X \<guillemotleft> move n i\<rparr> P'\<close>
      have "\<nu> a. \<P> a \<rightarrow>\<^sub>s\<lparr>A \<triangleleft>\<^bsub>Suc n\<^esub> X\<rparr> P' \<guillemotleft> move i n"
        by
          (simp only:
            synchronous_transition.scope_opening
            composition_adapted [symmetric]
            back_and_forth_moves identity_adapted
          )
      then have "\<nu> a. \<P> a \<parallel> Q \<rightarrow>\<^sub>s\<lparr>A \<triangleleft>\<^bsub>Suc n\<^esub> X\<rparr> P' \<guillemotleft> move i n \<parallel> Q \<guillemotleft> suffix (Suc n)"
        by (fact synchronous_transition.parallel_left_io)
      then show ?thesis
        unfolding \<open>\<alpha> = A \<triangleleft>\<^bsub>Suc n\<^esub> X\<close> and \<open>S = P' \<guillemotleft> move i n \<parallel> Q \<guillemotleft> suffix (Suc n)\<close>
        by (intro exI conjI, use in assumption) simp
    next
      case (parallel_right_io R)
      from \<open>Q \<guillemotleft> tail \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<triangleleft>\<^bsub>n\<^esub> X \<guillemotleft> move n i\<rparr> R\<close>
      obtain Y where "X \<guillemotleft> move n i = Y \<guillemotleft> on_suffix n tail"
        by (elim sending_transition_from_adapted)
      have "X = Y \<guillemotleft> remove i"
      proof -
        have "X = X \<guillemotleft> move n i \<guillemotleft> move i n"
          by (simp only: composition_adapted [symmetric] back_and_forth_moves identity_adapted)
        also have "\<dots> = Y \<guillemotleft> remove n \<guillemotleft> move i n"
          unfolding \<open>X \<guillemotleft> move n i = Y \<guillemotleft> on_suffix n tail\<close> and tail_def
          by transfer (simp add: comp_def)
        also have "\<dots> = Y \<guillemotleft> remove i"
          by (simp only: composition_adapted [symmetric] remove_after_move)
        finally show ?thesis .
      qed
      with \<open>dependent_on_chan_at i X\<close> have False
        by transfer (simp add: stake_shift sdrop_shift)
      then show ?thesis
        by (fact FalseE)
    qed
  next
    case (new_channel_io \<eta> A n X \<R>)
    from \<open>\<nabla> \<P> \<parallel> Q \<guillemotleft> tail \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> tail) n (X \<guillemotleft> remove n)\<rparr> \<nabla>\<^bsub>n\<^esub> \<R>\<close> show ?thesis
    proof cases
      case (parallel_left_io P')
      have "\<R> = (\<lambda>a. \<Delta>\<^bsub>n\<^esub> P' a \<parallel> Q \<guillemotleft> suffix n)"
      proof -
        have "\<R> = \<Delta>\<^bsub>n\<^esub> (\<nabla>\<^bsub>n\<^esub> \<R>)"
          by (simp only: deep_curry_after_deep_uncurry pointfree_idE)
        also have "\<dots> = \<Delta>\<^bsub>n\<^esub> (P' \<parallel> Q \<guillemotleft> suffix (Suc n))"
          unfolding \<open>\<nabla>\<^bsub>n\<^esub> \<R> = P' \<parallel> Q \<guillemotleft> tail \<guillemotleft> suffix n\<close> and tail_def
          by transfer simp
        also have "\<dots> = (\<lambda>a. \<Delta>\<^bsub>n\<^esub> P' a \<parallel> Q \<guillemotleft> suffix n)"
          by transfer (simp del: shift_simps(2), unfold sdrop_stl, simp add: sdrop_shift)
        finally show ?thesis .
      qed
      from \<open>\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> tail) n (X \<guillemotleft> remove n)\<rparr> P'\<close>
      have "\<nu> a. \<P> a \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> \<nu> a. \<Delta>\<^bsub>n\<^esub> P' a"
        by
          (simp only:
            deep_uncurry_after_deep_curry
            pointfree_idE
            synchronous_transition.new_channel_io
          )
      then have "\<nu> a. \<P> a \<parallel> Q \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> \<nu> a. \<Delta>\<^bsub>n\<^esub> P' a \<parallel> Q \<guillemotleft> suffix n"
        by (fact synchronous_transition.parallel_left_io)
      then show ?thesis
        unfolding \<open>\<alpha> = IO \<eta> A n X\<close> and \<open>S = \<nu> a. \<R> a\<close> and \<open>\<R> = (\<lambda>a. \<Delta>\<^bsub>n\<^esub> P' a \<parallel> Q \<guillemotleft> suffix n)\<close>
        using equality_in_universe
        by (intro exI conjI, use in assumption) force
    next
      case (parallel_right_io U)
      have "\<R> = (\<lambda>a. \<P> a \<guillemotleft> suffix n \<parallel> \<Delta>\<^bsub>n\<^esub> U a)"
      proof -
        have "\<R> = \<Delta>\<^bsub>n\<^esub> (\<nabla>\<^bsub>n\<^esub> \<R>)"
          by (simp only: deep_curry_after_deep_uncurry pointfree_idE)
        also have "\<dots> = \<Delta>\<^bsub>n\<^esub> (\<nabla> \<P> \<guillemotleft> suffix n \<parallel> U)"
          unfolding \<open>\<nabla>\<^bsub>n\<^esub> \<R> = \<nabla> \<P> \<guillemotleft> suffix n \<parallel> U\<close>
          using refl .
        also have "\<dots> = (\<lambda>a. \<P> a \<guillemotleft> suffix n \<parallel> \<Delta>\<^bsub>n\<^esub> U a)"
          by transfer (simp del: shift_simps(2), unfold sdrop_stl, simp add: sdrop_shift)
        finally show ?thesis .
      qed
      from \<open>Q \<guillemotleft> tail \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> tail) n (X \<guillemotleft> remove n)\<rparr> U\<close>
      have "Q \<guillemotleft> tail \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> tail) n (X \<guillemotleft> on_suffix n tail)\<rparr> U"
        unfolding tail_def
        by transfer (simp add: comp_def)
      then obtain Q' where "U = Q' \<guillemotleft> on_suffix n tail" and "Q \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> Q'"
        by
          (cases \<eta>)
          (
            blast elim: sending_transition_from_adapted,
            blast elim: adapted_receiving_transition_from_adapted
          )
      from \<open>U = Q' \<guillemotleft> on_suffix n tail\<close> have "U = Q' \<guillemotleft> remove n"
        unfolding tail_def
        by transfer (simp add: comp_def)
      then have "\<R> = (\<lambda>a. \<P> a \<guillemotleft> suffix n \<parallel> Q')"
        unfolding \<open>\<R> = (\<lambda>a. \<P> a \<guillemotleft> suffix n \<parallel> \<Delta>\<^bsub>n\<^esub> U a)\<close>
        by transfer (simp del: shift_simps(2) add: stake_shift sdrop_shift stake_sdrop)
      from \<open>Q \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> Q'\<close> have "\<nu> a. \<P> a \<parallel> Q \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> (\<nu> a. \<P> a) \<guillemotleft> suffix n \<parallel> Q'"
        by (fact synchronous_transition.parallel_right_io)
      then show ?thesis
        unfolding
          adapted_after_new_channel
        and
          \<open>\<alpha> = IO \<eta> A n X\<close> and \<open>S = \<nu> a. \<R> a\<close> and \<open>\<R> = (\<lambda>a. \<P> a \<guillemotleft> suffix n \<parallel> Q')\<close>
        using equality_in_universe
        by (intro exI conjI, use in assumption) force
    qed
  next
    case (new_channel_communication \<R>)
    from \<open>\<nabla> \<P> \<parallel> Q \<guillemotleft> tail \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<nabla> \<R>\<close> show ?thesis
    proof cases
      case (communication \<eta> \<mu> A' n X' P' U)
      show ?thesis
      proof (cases \<eta>)
        case Sending
        from \<open>\<eta> \<noteq> \<mu>\<close> and \<open>\<eta> = Sending\<close> have "\<mu> = Receiving"
          by (cases \<mu>) simp
        from \<open>Q \<guillemotleft> tail \<rightarrow>\<^sub>s\<lparr>IO \<mu> A' n X'\<rparr> U\<close> obtain A
          where "A' = A \<guillemotleft> tail" and "Q \<guillemotleft> remove 0 \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> remove 0 \<triangleright>\<^bsub>n\<^esub> X'\<rparr> U"
          unfolding tail_def and \<open>\<mu> = Receiving\<close>
          by (elim receiving_transition_from_adapted, transfer, simp add: comp_def)
        show ?thesis
        proof (cases "dependent_on_chan_at n X'")
          case True
          from \<open>\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X'\<rparr> P'\<close> have "\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<triangleleft>\<^bsub>n\<^esub> X' \<guillemotleft> move n n\<rparr> P' \<guillemotleft> move n n"
            unfolding \<open>\<eta> = Sending\<close> and \<open>A' = A \<guillemotleft> tail\<close>
            by (simp only: identity_as_move [symmetric] identity_adapted)
          with \<open>dependent_on_chan_at n X'\<close> have "\<nu> a. \<P> a \<rightarrow>\<^sub>s\<lparr>A \<triangleleft>\<^bsub>Suc n\<^esub> X'\<rparr> P'"
            by (simp only: scope_opening [where i = n])
          moreover
          from \<open>Q \<guillemotleft> remove 0 \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> remove 0 \<triangleright>\<^bsub>n\<^esub> X'\<rparr> U\<close> have "Q \<rightarrow>\<^sub>s\<lparr>A \<triangleright>\<^bsub>Suc n\<^esub> X'\<rparr> U"
            by
              (simp add:
                receiving_transition_with_remove_adapted_source_part
                identity_as_move [symmetric]
                identity_adapted
              )
          ultimately have "\<nu> a. \<P> a \<parallel> Q \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<star>\<^bsup>Suc n\<^esup> (P' \<parallel> U)"
            by (blast intro: synchronous_transition.communication)
          then show ?thesis
            unfolding
              funpow.simps(2) and new_channel_as_create_channel and comp_def
            and
              \<open>\<alpha> = \<tau>\<close> and \<open>S = \<nu> a. \<R> a\<close> and \<open>\<nabla> \<R> = \<star>\<^bsup>n\<^esup> (P' \<parallel> U)\<close>
            by (intro exI conjI, use in assumption) simp
        next
          case False
          then obtain X where "X' = X \<guillemotleft> remove n"
            by (erule not_dependent_on_chan_at)
          from \<open>\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X'\<rparr> P'\<close>
          have left_transition: "\<nu> a. \<P> a \<rightarrow>\<^sub>s\<lparr>A \<triangleleft>\<^bsub>n\<^esub> X\<rparr> \<nu> a. \<Delta>\<^bsub>n\<^esub> P' a"
            unfolding \<open>\<eta> = Sending\<close> and \<open>A' = A \<guillemotleft> tail\<close> and \<open>X' = X \<guillemotleft> remove n\<close>
            by (simp only: new_channel_io deep_uncurry_after_deep_curry pointfree_idE)
          from \<open>Q \<guillemotleft> remove 0 \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> remove 0 \<triangleright>\<^bsub>n\<^esub> X'\<rparr> U\<close>
          have "Q \<guillemotleft> remove 0 \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> remove 0 \<triangleright>\<^bsub>n\<^esub> X \<guillemotleft> on_suffix n (remove 0)\<rparr> U"
            unfolding \<open>X' = X \<guillemotleft> remove n\<close>
            by (simp add: on_suffix_remove)
          then obtain Q'
            where "U = Q' \<guillemotleft> on_suffix n (remove 0)" and right_transition: "Q \<rightarrow>\<^sub>s\<lparr>A \<triangleright>\<^bsub>n\<^esub> X\<rparr> Q'"
            by (erule adapted_receiving_transition_from_adapted)
          from \<open>U = Q' \<guillemotleft> on_suffix n (remove 0)\<close> have "U = Q' \<guillemotleft> remove n"
            by (simp add: on_suffix_remove)
          from left_transition and right_transition
          have "\<nu> a. \<P> a \<parallel> Q \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<star>\<^bsup>n\<^esup> (\<nu> a. \<Delta>\<^bsub>n\<^esub> P' a \<parallel> Q')"
            by (blast intro: synchronous_transition.communication)
          then show ?thesis
            unfolding
              new_channel_as_create_channel and comp_def
            and
              \<open>\<alpha> = \<tau>\<close> and \<open>S = \<nu> a. \<R> a\<close> and \<open>\<nabla> \<R> = \<star>\<^bsup>n\<^esup> (P' \<parallel> U)\<close> and \<open>U = Q' \<guillemotleft> remove n\<close>
            using
              independent_value_adjustment [where n = n and P' = P' and Q' = Q']
            and
              power_in_universe [OF create_channel_mutation_in_universe]
            by (intro exI conjI, use in assumption) force
        qed
      next
        case Receiving
        from \<open>\<eta> \<noteq> \<mu>\<close> and \<open>\<eta> = Receiving\<close> have "\<mu> = Sending"
          by (cases \<mu>) simp_all
        from \<open>Q \<guillemotleft> tail \<rightarrow>\<^sub>s\<lparr>IO \<mu> A' n X'\<rparr> U\<close>
        obtain A and X and Q'
          where
            "A' = A \<guillemotleft> tail"
          and
            "X' = X \<guillemotleft> on_suffix n tail"
          and
            "U = Q' \<guillemotleft> on_suffix n tail"
          and
            "Q \<rightarrow>\<^sub>s\<lparr>A \<triangleleft>\<^bsub>n\<^esub> X\<rparr> Q'"
          unfolding \<open>\<mu> = Sending\<close>
          by (erule sending_transition_from_adapted)
        from \<open>X' = X \<guillemotleft> on_suffix n tail\<close> and \<open>U = Q' \<guillemotleft> on_suffix n tail\<close>
        have "X' = X \<guillemotleft> remove n" and "U = Q' \<guillemotleft> remove n"
          unfolding tail_def
          by (transfer, simp add: comp_def)+
        from \<open>\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X'\<rparr> P'\<close> have "\<nu> a. \<P> a \<rightarrow>\<^sub>s\<lparr>A \<triangleright>\<^bsub>n\<^esub> X\<rparr> \<nu> a. \<Delta>\<^bsub>n\<^esub> P' a"
            unfolding \<open>\<eta> = Receiving\<close> and \<open>A' = A \<guillemotleft> tail\<close> and \<open>X' = X \<guillemotleft> remove n\<close>
            by (simp only: new_channel_io deep_uncurry_after_deep_curry pointfree_idE)
        with \<open>Q \<rightarrow>\<^sub>s\<lparr>A \<triangleleft>\<^bsub>n\<^esub> X\<rparr> Q'\<close> have "\<nu> a. \<P> a \<parallel> Q \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<star>\<^bsup>n\<^esup> (\<nu> a. \<Delta>\<^bsub>n\<^esub> P' a \<parallel> Q')"
          by (blast intro: synchronous_transition.communication)
        then show ?thesis
          unfolding
            new_channel_as_create_channel and comp_def
          and
            \<open>\<alpha> = \<tau>\<close> and \<open>S = \<nu> a. \<R> a\<close> and \<open>\<nabla> \<R> = \<star>\<^bsup>n\<^esup> (P' \<parallel> U)\<close> and \<open>U = Q' \<guillemotleft> remove n\<close>
          using
            independent_value_adjustment [where n = n and P' = P' and Q' = Q']
          and
            power_in_universe [OF create_channel_mutation_in_universe]
          by (intro exI conjI, use in assumption) force
      qed
    next
      case (parallel_left_communication P')
      have "\<R> = (\<lambda>a. \<Delta> P' a \<parallel> Q)"
      proof -
        have "\<R> = \<Delta> (\<nabla> \<R>)"
          by simp
        also have "\<dots> = \<Delta> (P' \<parallel> Q \<guillemotleft> tail)"
          unfolding \<open>\<nabla> \<R> = P' \<parallel> Q \<guillemotleft> tail\<close>
          using refl .
        also have "\<dots> = (\<lambda>a. \<Delta> P' a \<parallel> Q)"
          unfolding tail_def
          by transfer simp
        finally show ?thesis .
      qed
      from \<open>\<nabla> \<P> \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> P'\<close> have "\<nu> a. \<P> a \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<nu> a. \<Delta> P' a"
        by (intro synchronous_transition.new_channel_communication) simp
      then have "\<nu> a. \<P> a \<parallel> Q \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<nu> a. \<Delta> P' a \<parallel> Q"
        by (fact synchronous_transition.parallel_left_communication)
      then show ?thesis
        unfolding \<open>\<alpha> = \<tau>\<close> and \<open>S = \<nu> a. \<R> a\<close> and \<open>\<R> = (\<lambda>a. \<Delta> P' a \<parallel> Q)\<close>
        using equality_in_universe
        by (intro exI conjI, use in assumption) force
    next
      case (parallel_right_communication U)
      have "\<R> = (\<lambda>a. \<P> a \<parallel> \<Delta> U a)"
      proof -
        have "\<R> = \<Delta> (\<nabla> \<R>)"
          by simp
        also have "\<dots> = \<Delta> (\<nabla> \<P> \<parallel> U)"
          unfolding \<open>\<nabla> \<R> = \<nabla> \<P> \<parallel> U\<close>
          using refl .
        also have "\<dots> = (\<lambda>a. \<P> a \<parallel> \<Delta> U a)"
          by simp
        finally show ?thesis .
      qed
      from \<open>Q \<guillemotleft> tail \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> U\<close> obtain Q' where "U = Q' \<guillemotleft> tail" and "Q \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> Q'"
        by (erule communication_transition_from_adapted)
      have "\<R> = (\<lambda>a. \<P> a \<parallel> Q')"
        unfolding \<open>\<R> = (\<lambda>a. \<P> a \<parallel> \<Delta> U a)\<close> and \<open>U = Q' \<guillemotleft> tail\<close> and tail_def
        by transfer simp
      from \<open>Q \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> Q'\<close> have "\<nu> a. \<P> a \<parallel> Q \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<nu> a. \<P> a \<parallel> Q'"
        by (fact synchronous_transition.parallel_right_communication)
      then show ?thesis
        unfolding \<open>\<alpha> = \<tau>\<close> and \<open>S = \<nu> a. \<R> a\<close> and \<open>\<R> = (\<lambda>a. \<P> a \<parallel> Q')\<close>
        using equality_in_universe
        by (intro exI conjI, use in assumption) force
    qed
  qed
qed respectful

end

lemma tagged_parallel_left_scope_extension [thorn_simps]:
  shows "\<langle>t\<rangle> \<nu> a. \<P> a \<parallel> Q \<sim>\<^sub>s \<langle>t\<rangle> \<nu> a. (\<P> a \<parallel> Q)"
  unfolding tagged_new_channel_def
  using parallel_left_scope_extension .

lemma parallel_right_scope_extension [thorn_simps]:
  fixes \<Q> :: "chan \<Rightarrow> process family"
  shows "P \<parallel> \<nu> a. \<Q> a \<sim>\<^sub>s \<nu> a. (P \<parallel> \<Q> a)"
proof -
  have "P \<parallel> \<nu> a. \<Q> a \<sim>\<^sub>s \<nu> a. \<Q> a \<parallel> P"
    using parallel_commutativity .
  also have "\<dots> \<sim>\<^sub>s \<nu> a. (\<Q> a \<parallel> P)"
    using parallel_left_scope_extension .
  also have "\<dots> \<sim>\<^sub>s \<nu> a. (P \<parallel> \<Q> a)"
    using parallel_commutativity
    by process_family_equivalence
  finally show ?thesis .
qed

lemma tagged_parallel_right_scope_extension [thorn_simps]:
  shows "P \<parallel> \<langle>t\<rangle> \<nu> a. \<Q> a \<sim>\<^sub>s \<langle>t\<rangle> \<nu> a. (P \<parallel> \<Q> a)"
  unfolding tagged_new_channel_def
  using parallel_right_scope_extension .

context begin

private lemma communication_with_rightmost_adjustment:
  shows "\<star>\<^bsup>n\<^esup> (Q \<guillemotleft> suffix n \<parallel> T) \<sim>\<^sub>s Q \<parallel> \<star>\<^bsup>n\<^esup> T"
proof (induction n arbitrary: T)
  case 0
  show ?case
    by transfer simp
next
  case (Suc n)
  have "\<star>\<^bsup>Suc n\<^esup> (Q \<guillemotleft> suffix (Suc n) \<parallel> T) \<sim>\<^sub>s \<star>\<^bsup>n\<^esup> (\<nu> a. (Q \<guillemotleft> suffix n \<parallel> \<Delta> T a))"
    unfolding funpow_Suc_right
    by transfer simp
  also have "\<dots> \<sim>\<^sub>s \<star>\<^bsup>n\<^esup> (Q \<guillemotleft> suffix n \<parallel> \<nu> a. \<Delta> T a)"
    by
      (blast intro:
        parallel_right_scope_extension
        synchronous.bisimilarity_symmetry_rule
        synchronous.create_channel_power_is_compatible_with_bisimilarity
      )
  also have "\<dots> \<sim>\<^sub>s Q \<parallel> \<star>\<^bsup>n\<^esup> (\<nu> a. \<Delta> T a)"
    using Suc.IH .
  also have "\<dots> \<sim>\<^sub>s Q \<parallel> \<star>\<^bsup>Suc n\<^esup> T"
    unfolding funpow_Suc_right
    by simp
  finally show ?case .
qed

lemma parallel_left_commutativity [thorn_simps]:
  shows "P \<parallel> (Q \<parallel> R) \<sim>\<^sub>s Q \<parallel> (P \<parallel> R)"
proof (coinduction arbitrary: P Q R rule: synchronous.symmetric_up_to_rule [where \<F> = "[\<sim>\<^sub>s] \<frown> \<M> \<frown> [\<sim>\<^sub>s]"])
  case (simulation \<alpha> S P Q R)
  then show ?case
  proof cases
    case (communication \<eta> \<mu> A n X P' U)
    from \<open>Q \<parallel> R \<rightarrow>\<^sub>s\<lparr>IO \<mu> A n X\<rparr> U\<close> show ?thesis
    proof cases
      case (parallel_left_io Q')
      from \<open>P \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> P'\<close> have "P \<parallel> R \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> P' \<parallel> R \<guillemotleft> suffix n"
        by (fact synchronous_transition.parallel_left_io)
      with \<open>\<eta> \<noteq> \<mu>\<close> and \<open>Q \<rightarrow>\<^sub>s\<lparr>IO \<mu> A n X\<rparr> Q'\<close> have "Q \<parallel> (P \<parallel> R) \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<star>\<^bsup>n\<^esup> (Q' \<parallel> (P' \<parallel> R \<guillemotleft> suffix n))"
        by (intro synchronous_transition.communication [where \<eta> = \<mu> and \<mu> = \<eta>]) simp
      then show ?thesis
        unfolding \<open>\<alpha> = \<tau>\<close> and \<open>S = \<star>\<^bsup>n\<^esup> (P' \<parallel> U)\<close> and \<open>U = Q' \<parallel> R \<guillemotleft> suffix n\<close>
        using power_in_universe [OF create_channel_mutation_in_universe]
        by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
    next
      case (parallel_right_io R')
      from \<open>\<eta> \<noteq> \<mu>\<close> and \<open>P \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> P'\<close> and \<open>R \<rightarrow>\<^sub>s\<lparr>IO \<mu> A n X\<rparr> R'\<close>
      have "P \<parallel> R \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<star>\<^bsup>n\<^esup> (P' \<parallel> R')"
        by (fact synchronous_transition.communication)
      then have "Q \<parallel> (P \<parallel> R) \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> Q \<parallel> \<star>\<^bsup>n\<^esup> (P' \<parallel> R')"
        by (fact parallel_right_communication)
      then show ?thesis
        unfolding \<open>\<alpha> = \<tau>\<close> and \<open>S = \<star>\<^bsup>n\<^esup> (P' \<parallel> U)\<close> and \<open>U = Q \<guillemotleft> suffix n \<parallel> R'\<close>
        using
          communication_with_rightmost_adjustment
        and
          power_in_universe [OF create_channel_mutation_in_universe]
        by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
    qed
  next
    case (parallel_left_io \<eta> A n X P')
    from \<open>P \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> P'\<close> have "P \<parallel> R \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> P' \<parallel> R \<guillemotleft> suffix n"
      by (fact synchronous_transition.parallel_left_io)
    then have "Q \<parallel> (P \<parallel> R) \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> Q \<guillemotleft> suffix n \<parallel> (P' \<parallel> R \<guillemotleft> suffix n)"
      by (fact parallel_right_io)
    then show ?thesis
      unfolding \<open>\<alpha> = IO \<eta> A n X\<close> and \<open>S = P' \<parallel> (Q \<parallel> R) \<guillemotleft> suffix n\<close> [unfolded adapted_after_parallel]
      using equality_in_universe
      by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
  next
    case (parallel_left_communication P')
    from \<open>P \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> P'\<close> have "P \<parallel> R \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> P' \<parallel> R"
      by (fact synchronous_transition.parallel_left_communication)
    then have "Q \<parallel> (P \<parallel> R) \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> Q \<parallel> (P' \<parallel> R)"
      by (fact parallel_right_communication)
    then show ?thesis
      unfolding \<open>\<alpha> = \<tau>\<close> and \<open>S = P' \<parallel> (Q \<parallel> R)\<close>
      using equality_in_universe
      by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
  next
    case (parallel_right_io \<eta> A n X U)
    from \<open>Q \<parallel> R \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> U\<close> show ?thesis
    proof cases
      case (parallel_left_io Q')
      from \<open>Q \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> Q'\<close> have "Q \<parallel> (P \<parallel> R) \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> Q' \<parallel> (P \<parallel> R) \<guillemotleft> suffix n"
        by (fact synchronous_transition.parallel_left_io)
      then show ?thesis
        unfolding
          adapted_after_parallel
        and
          \<open>\<alpha> = IO \<eta> A n X\<close> and \<open>S = P \<guillemotleft> suffix n \<parallel> U\<close> and \<open>U = Q' \<parallel> R \<guillemotleft> suffix n\<close>
        using equality_in_universe
        by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
    next
      case (parallel_right_io R')
      from \<open>R \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> R'\<close> have "P \<parallel> R \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> P \<guillemotleft> suffix n \<parallel> R'"
        by (fact synchronous_transition.parallel_right_io)
      then have "Q \<parallel> (P \<parallel> R) \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> Q \<guillemotleft> suffix n \<parallel> (P \<guillemotleft> suffix n \<parallel> R')"
        by (fact synchronous_transition.parallel_right_io)
      then show ?thesis
        unfolding \<open>\<alpha> = IO \<eta> A n X\<close> and \<open>S = P \<guillemotleft> suffix n \<parallel> U\<close> and \<open>U = Q \<guillemotleft> suffix n \<parallel> R'\<close>
        using equality_in_universe
        by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
    qed
  next
    case (parallel_right_communication U)
    from \<open>Q \<parallel> R \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> U\<close> show ?thesis
    proof cases
      case (communication \<eta> \<mu> A n X Q' R')
      from \<open>R \<rightarrow>\<^sub>s\<lparr>IO \<mu> A n X\<rparr> R'\<close> have "P \<parallel> R \<rightarrow>\<^sub>s\<lparr>IO \<mu> A n X\<rparr> P \<guillemotleft> suffix n \<parallel> R'"
        by (fact parallel_right_io)
      with \<open>\<eta> \<noteq> \<mu>\<close> and \<open>Q \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> Q'\<close> have "Q \<parallel> (P \<parallel> R) \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<star>\<^bsup>n\<^esup> (Q' \<parallel> (P \<guillemotleft> suffix n \<parallel> R'))"
        by (fact synchronous_transition.communication)
      then show ?thesis
        unfolding \<open>\<alpha> = \<tau>\<close> and \<open>S = P \<parallel> U\<close> and \<open>U = \<star>\<^bsup>n\<^esup> (Q' \<parallel> R')\<close>
        using
          communication_with_rightmost_adjustment [THEN synchronous.bisimilarity_symmetry_rule]
        and
          power_in_universe [OF create_channel_mutation_in_universe]
        by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
    next
      case (parallel_left_communication Q')
      from \<open>Q \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> Q'\<close> have "Q \<parallel> (P \<parallel> R) \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> Q' \<parallel> (P \<parallel> R)"
        by (fact synchronous_transition.parallel_left_communication)
      then show ?thesis
        unfolding \<open>\<alpha> = \<tau>\<close> and \<open>S = P \<parallel> U\<close> and \<open>U = Q' \<parallel> R\<close>
        using equality_in_universe
        by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
    next
      case (parallel_right_communication R')
      from \<open>R \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> R'\<close> have "P \<parallel> R \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> P \<parallel> R'"
        by (fact synchronous_transition.parallel_right_communication)
      then have "Q \<parallel> (P \<parallel> R) \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> Q \<parallel> (P \<parallel> R')"
        by (fact synchronous_transition.parallel_right_communication)
      then show ?thesis
        unfolding \<open>\<alpha> = \<tau>\<close> and \<open>S = P \<parallel> U\<close> and \<open>U = Q \<parallel> R'\<close>
        using equality_in_universe
        by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
    qed
  qed
qed (respectful, iprover)

end

declare parallel_commutativity [thorn_simps]

(*FIXME: Maybe reprove commutativity of parallel composition. *)

lemma parallel_associativity [thorn_simps]:
  shows "(P \<parallel> Q) \<parallel> R \<sim>\<^sub>s P \<parallel> (Q \<parallel> R)"
proof -
  have "(P \<parallel> Q) \<parallel> R \<sim>\<^sub>s R \<parallel> (P \<parallel> Q)"
    using parallel_commutativity .
  also have "\<dots> \<sim>\<^sub>s P \<parallel> (R \<parallel> Q)"
    using parallel_left_commutativity .
  also have "\<dots> \<sim>\<^sub>s P \<parallel> (Q \<parallel> R)"
    using parallel_commutativity
    by equivalence
  finally show ?thesis .
qed

lemma parallel_left_identity [thorn_simps]:
  shows "\<zero> \<parallel> P \<sim>\<^sub>s P"
proof (coinduction arbitrary: P rule: synchronous.up_to_rule [where \<F> = id])
  case (forward_simulation \<alpha> S P)
  then show ?case
  proof cases
    case (communication \<eta> \<mu> A n X U P')
    from \<open>\<zero> \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> U\<close> show ?thesis
      by cases
  next
    case (parallel_left_io \<eta> A n X U)
    from \<open>\<zero> \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> U\<close> show ?thesis
      by cases
  next
    case (parallel_left_communication U)
    from \<open>\<zero> \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> U\<close> show ?thesis
      by cases
  next
    case (parallel_right_io \<eta> A n X P')
    from \<open>P \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> P'\<close> show ?thesis
      unfolding \<open>\<alpha> = IO \<eta> A n X\<close> and \<open>S = \<zero> \<guillemotleft> suffix n \<parallel> P'\<close> [unfolded adapted_after_stop]
      by (intro exI conjI, use in assumption) simp
  next
    case (parallel_right_communication P')
    from \<open>P \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> P'\<close> show ?thesis
      unfolding \<open>\<alpha> = \<tau>\<close> and \<open>S = \<zero> \<parallel> P'\<close>
      by (intro exI conjI, use in assumption) simp
  qed
next
  case (backward_simulation \<alpha> P' P)
  have "\<zero> \<parallel> P \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> \<zero> \<parallel> P'"
  proof (cases \<alpha>)
    case (IO \<eta> A n X)
    from \<open>P \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> P'\<close> have "\<zero> \<parallel> P \<rightarrow>\<^sub>s\<lparr>IO \<eta> A n X\<rparr> \<zero> \<guillemotleft> suffix n \<parallel> P'"
      unfolding \<open>\<alpha> = IO \<eta> A n X\<close>
      by (fact parallel_right_io)
    then show ?thesis
      unfolding \<open>\<alpha> = IO \<eta> A n X\<close>
      by (simp only: adapted_after_stop)
  next
    case Communication
    from \<open>P \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> P'\<close> show ?thesis
      unfolding \<open>\<alpha> = \<tau>\<close>
      by (fact parallel_right_communication)
  qed
  then show ?case
    by (intro exI conjI, use in assumption) simp
qed respectful

lemma parallel_right_identity [thorn_simps]:
  shows "P \<parallel> \<zero> \<sim>\<^sub>s P"
proof -
  have "P \<parallel> \<zero> \<sim>\<^sub>s \<zero> \<parallel> P"
    using parallel_commutativity
    by equivalence
  also have "\<dots> \<sim>\<^sub>s P"
    using parallel_left_identity .
  finally show ?thesis .
qed

context begin

private lemma stop_scope_redundancy:
  shows "\<nu> _ :: chan. \<zero> \<sim>\<^sub>s \<zero>"
proof (coinduction rule: synchronous.up_to_rule [where \<F> = \<bottom>])
  case (forward_simulation \<alpha> S)
  from \<open>\<nu> _. \<zero> \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> S\<close> show ?case
  proof cases
    case (scope_opening i n X A)
    from \<open>\<zero> \<rightarrow>\<^sub>s\<lparr>A \<guillemotleft> tail \<triangleleft>\<^bsub>n\<^esub> X \<guillemotleft> move n i\<rparr> S \<guillemotleft> move n i\<close> show ?thesis
      by cases
  next
    case (new_channel_io \<eta> A n X \<Q>)
    from \<open>\<zero> \<rightarrow>\<^sub>s\<lparr>IO \<eta> (A \<guillemotleft> tail) n (X \<guillemotleft> remove n)\<rparr> \<nabla>\<^bsub>n\<^esub> \<Q>\<close> show ?thesis
      by cases
  next
    case (new_channel_communication \<Q>)
    from \<open>\<zero> \<rightarrow>\<^sub>s\<lparr>\<tau>\<rparr> \<nabla> \<Q>\<close> show ?thesis
      by cases
  qed
next
  case (backward_simulation \<alpha> S)
  from \<open>\<zero> \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> S\<close> show ?case
    by cases
qed respectful

lemma scope_redundancy [thorn_simps]:
  shows "\<nu> _ :: chan. P \<sim>\<^sub>s P"
proof -
  have "\<nu> _ :: chan. P \<sim>\<^sub>s \<nu> _ :: chan. (\<zero> \<parallel> P)"
    using parallel_left_identity
    by process_family_equivalence
  also have "\<dots> \<sim>\<^sub>s \<nu> _ :: chan. \<zero> \<parallel> P"
    using parallel_left_scope_extension
    by process_family_equivalence
  also have "\<dots> \<sim>\<^sub>s \<zero> \<parallel> P"
    using stop_scope_redundancy
    by process_family_equivalence
  also have "\<dots> \<sim>\<^sub>s P"
    using parallel_left_identity .
  finally show ?thesis .
qed

end

text \<open>
  We extend \<^theory_text>\<open>thorn_simps\<close> with rules for eliminating duplicates of \<open>\<triangleright>\<^sup>\<infinity>\<close>-processes, which are
  based on the observation that \<^const>\<open>repeated_receive\<close> is idempotent.

  Incidentally, duplicate removal based on idempotence plays rather well with associativity and
  commutativity rules. The reason is the simplifier's handling of permutative rules, like
  commutativity: these rules are applied only when they lead to a smaller term, where ``smaller'' by
  default means ``lexicographically smaller'' (see Subsection~9.3.3 of the Isabelle/Isar Reference
  Manual). A result of this behavior is that equal processes in a chain of parallel compositions
  will sooner or later stand next to each other. If then a pair of equal processes stands at the end
  of the chain, it can be collapsed by applying an idempotency rule; if it does not stand at the
  end, it can be collapsed by a ``nested'' variant of an idempotency rule, analogous to the
  ``nested'' variant of commutativity.
\<close>
(* FIXME:
  Add a proper reference to the reference manual.
*)
(*FIXME:
  Don't say ``nested'' but use terminology analogous to the new terminology used for ``nested''
  commutativity rules.
*)

context begin

private lemma left_amended_double_suffix_adapted:
  shows "(R \<parallel> P \<guillemotleft> suffix n) \<parallel> Q \<guillemotleft> suffix n \<sim>\<^sub>s R \<parallel> (P \<parallel> Q) \<guillemotleft> suffix n"
  unfolding adapted_after_parallel
  using parallel_associativity .

private lemma right_amended_double_suffix_adapted:
  shows "P \<guillemotleft> suffix n \<parallel> (R \<parallel> Q \<guillemotleft> suffix n) \<sim>\<^sub>s R \<parallel> (P \<parallel> Q) \<guillemotleft> suffix n"
  unfolding adapted_after_parallel
  using parallel_left_commutativity .

lemma repeated_receive_idempotency [thorn_simps]:
  fixes A :: "chan family" and \<P> :: "val \<Rightarrow> process family"
  shows "A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x \<sim>\<^sub>s A \<triangleright>\<^sup>\<infinity> x. \<P> x"
proof (coinduction rule: synchronous.up_to_rule [where \<F> = "[\<sim>\<^sub>s] \<frown> \<M>"])
  case (forward_simulation \<alpha> S)
  then show ?case
  proof cases
    case (parallel_left_io \<eta> A' n X Q)
    from \<open>A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> Q\<close> obtain T where "Q = T \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
      by (fast elim: transition_from_repeated_receive)
    with \<open>A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> Q\<close>
    have "A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> T \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
      by (simp only:)
    then show ?thesis
      unfolding
        \<open>\<alpha> = IO \<eta> A' n X\<close> and \<open>S = Q \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n\<close>
      and
        \<open>Q = T \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n\<close>
      using
        left_amended_double_suffix_adapted
      and
        composition_in_universe
          [OF suffix_adapted_mutation_in_universe parallel_mutation_in_universe]
      by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
  next
    case (parallel_right_io \<eta> A' n X Q)
    from \<open>A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> Q\<close> obtain T where "Q = T \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
      by (fast elim: transition_from_repeated_receive)
    with \<open>A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> Q\<close>
    have "A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> T \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
      by (simp only:)
    then show ?thesis
      unfolding
        \<open>\<alpha> = IO \<eta> A' n X\<close> and \<open>S = (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n \<parallel> Q\<close>
      and
        \<open>Q = T \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n\<close>
      using
        right_amended_double_suffix_adapted
      and
        composition_in_universe
          [OF suffix_adapted_mutation_in_universe parallel_mutation_in_universe]
      by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
  qed (blast elim: transition_from_repeated_receive)+
next
  case (backward_simulation \<alpha> S)
  from \<open>A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> S\<close>
  obtain n and X where "\<alpha> = A \<triangleright>\<^bsub>n\<^esub> X" and "S = post_receive n X \<P> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
    by (erule transition_from_repeated_receive)
  with \<open>A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>\<alpha>\<rparr> S\<close>
  have "A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>A \<triangleright>\<^bsub>n\<^esub> X\<rparr> post_receive n X \<P> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
    by (simp only:)
  then have "
    A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x
    \<rightarrow>\<^sub>s\<lparr>A \<triangleright>\<^bsub>n\<^esub> X\<rparr>
    (post_receive n X \<P> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n) \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
    by (fact parallel_left_io)
  then show ?case
    unfolding
      \<open>\<alpha> = A \<triangleright>\<^bsub>n\<^esub> X\<close> and \<open>S = post_receive n X \<P> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n\<close>
    using
      left_amended_double_suffix_adapted
    and
      composition_in_universe
        [OF suffix_adapted_mutation_in_universe parallel_mutation_in_universe]
    by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
qed respectful

lemma repeated_receive_nested_idempotency [thorn_simps]:
  fixes A :: "chan family" and \<P> :: "val \<Rightarrow> process family"
  shows "A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> Q) \<sim>\<^sub>s A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> Q"
proof -
  have "A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> Q) \<sim>\<^sub>s (A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<parallel> Q"
    using parallel_associativity
    by equivalence
  also have "\<dots> \<sim>\<^sub>s A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> Q"
    using repeated_receive_idempotency
    by equivalence
  finally show ?thesis .
qed

private lemma with_inner_repeated_receive_post_right_receive:
  fixes A B :: "chan family" and \<P> \<Q> :: "val \<Rightarrow> process family"
  shows "
    (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n \<parallel>
    (((A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n \<parallel> post_receive n X \<Q>) \<parallel> (B \<triangleright>\<^sup>\<infinity> y. (A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> \<Q> y)) \<guillemotleft> suffix n)
    \<sim>\<^sub>s
    post_receive n X \<Q> \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> B \<triangleright>\<^sup>\<infinity> y. (A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> \<Q> y)) \<guillemotleft> suffix n"
    (is "?S \<sim>\<^sub>s ?T")
proof -
  have "?S \<sim>\<^sub>s
    (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n \<parallel> post_receive n X \<Q> \<parallel> (B \<triangleright>\<^sup>\<infinity> y. (A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> \<Q> y)) \<guillemotleft> suffix n"
    unfolding adapted_after_repeated_receive
    using repeated_receive_nested_idempotency and parallel_associativity
    by equivalence
  also have "\<dots> \<sim>\<^sub>s ?T"
    unfolding adapted_after_parallel
    using parallel_left_commutativity .
  finally show ?thesis .
qed

lemma inner_repeated_receive_redundancy:
  fixes A B :: "chan family" and \<P> \<Q> :: "val \<Rightarrow> process family"
  shows "A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> B \<triangleright>\<^sup>\<infinity> y. (A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> \<Q> y) \<sim>\<^sub>s A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> B \<triangleright>\<^sup>\<infinity> y. \<Q> y"
proof (coinduction rule: synchronous.up_to_rule [where \<F> = "[\<sim>\<^sub>s] \<frown> \<M> \<frown> [\<sim>\<^sub>s]"])
  case (forward_simulation \<alpha> S)
  then show ?case
  proof cases
    case (parallel_left_io \<eta> A' n X R)
    from \<open>A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> R\<close> obtain T where "R = T \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
      by (fast elim: transition_from_repeated_receive)
    with \<open>A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> R\<close>
    have "A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> T \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
      by (simp only:)
    then have "
      A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> B \<triangleright>\<^sup>\<infinity> y. \<Q> y
      \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr>
      (T \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n) \<parallel> (B \<triangleright>\<^sup>\<infinity> y. \<Q> y) \<guillemotleft> suffix n"
      by (fact synchronous_transition.parallel_left_io)
    then show ?thesis
      unfolding
        \<open>\<alpha> = IO \<eta> A' n X\<close> and \<open>S = R \<parallel> (B \<triangleright>\<^sup>\<infinity> y. (A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> \<Q> y)) \<guillemotleft> suffix n\<close>
      and
        \<open>R = T \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n\<close>
      using
        left_amended_double_suffix_adapted
      and
        left_amended_double_suffix_adapted [symmetric]
      and
        composition_in_universe
          [OF suffix_adapted_mutation_in_universe parallel_mutation_in_universe]
      by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
  next
    case (parallel_right_io \<eta> B' n Y R)
    from \<open>B \<triangleright>\<^sup>\<infinity> y. (A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> \<Q> y) \<rightarrow>\<^sub>s\<lparr>IO \<eta> B' n Y\<rparr> R\<close>
    have
      "\<eta> = Receiving"
    and
      "B' = B"
    and
      "R = post_receive n Y (\<lambda>y. A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> \<Q> y) \<parallel> (B \<triangleright>\<^sup>\<infinity> y. (A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> \<Q> y)) \<guillemotleft> suffix n"
      by (fast elim: transition_from_repeated_receive)+
    have "B \<triangleright>\<^sup>\<infinity> y. \<Q> y \<rightarrow>\<^sub>s\<lparr>B \<triangleright>\<^bsub>n\<^esub> Y\<rparr> post_receive n Y \<Q> \<parallel> (B \<triangleright>\<^sup>\<infinity> y. \<Q> y) \<guillemotleft> suffix n"
      using repeated_receive_transition .
    then have "
      A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> B \<triangleright>\<^sup>\<infinity> y. \<Q> y
      \<rightarrow>\<^sub>s\<lparr>B \<triangleright>\<^bsub>n\<^esub> Y\<rparr>
      (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n \<parallel> post_receive n Y \<Q> \<parallel> (B \<triangleright>\<^sup>\<infinity> y. \<Q> y) \<guillemotleft> suffix n"
      by (fact synchronous_transition.parallel_right_io)
    then show ?thesis
      unfolding
        post_receive_after_parallel
      and
        \<open>\<alpha> = IO \<eta> B' n Y\<close> and \<open>S = (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n \<parallel> R\<close>
      and
        \<open>\<eta> = Receiving\<close>
      and
        \<open>B' = B\<close>
      and
        \<open>R = post_receive n Y (\<lambda>y. A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> \<Q> y) \<parallel> (B \<triangleright>\<^sup>\<infinity> y. (A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> \<Q> y)) \<guillemotleft> suffix n\<close>
      using
        with_inner_repeated_receive_post_right_receive
      and
        right_amended_double_suffix_adapted [symmetric]
      and
        composition_in_universe
          [OF suffix_adapted_mutation_in_universe parallel_mutation_in_universe]
      by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
  qed (blast elim: transition_from_repeated_receive)+
next
  case (backward_simulation \<alpha> S)
  then show ?case
  proof cases
    case (parallel_left_io \<eta> A' n X R)
    from \<open>A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> R\<close> obtain T where "R = T \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
      by (fast elim: transition_from_repeated_receive)
    with \<open>A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> R\<close>
    have "A \<triangleright>\<^sup>\<infinity> x. \<P> x \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr> T \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n"
      by (simp only:)
    then have "
      A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> B \<triangleright>\<^sup>\<infinity> y. (A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> \<Q> y)
      \<rightarrow>\<^sub>s\<lparr>IO \<eta> A' n X\<rparr>
      (T \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n) \<parallel> (B \<triangleright>\<^sup>\<infinity> y. (A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> \<Q> y)) \<guillemotleft> suffix n"
      by (fact synchronous_transition.parallel_left_io)
    then show ?thesis
      unfolding
        \<open>\<alpha> = IO \<eta> A' n X\<close> and \<open>S = R \<parallel> (B \<triangleright>\<^sup>\<infinity> y. \<Q> y) \<guillemotleft> suffix n\<close>
      and
        \<open>R = T \<parallel> (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n\<close>
      using
        left_amended_double_suffix_adapted
      and
        left_amended_double_suffix_adapted [symmetric]
      and
        composition_in_universe
          [OF suffix_adapted_mutation_in_universe parallel_mutation_in_universe]
      by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
  next
    case (parallel_right_io \<eta> B' n Y R)
    from \<open>B \<triangleright>\<^sup>\<infinity> y. \<Q> y \<rightarrow>\<^sub>s\<lparr>IO \<eta> B' n Y\<rparr> R\<close>
    have
      "\<eta> = Receiving"
    and
      "B' = B"
    and
      "R = post_receive n Y \<Q> \<parallel> (B \<triangleright>\<^sup>\<infinity> y. \<Q> y) \<guillemotleft> suffix n"
      by (fast elim: transition_from_repeated_receive)+
    have "
      B \<triangleright>\<^sup>\<infinity> y. (A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> \<Q> y)
      \<rightarrow>\<^sub>s\<lparr>B \<triangleright>\<^bsub>n\<^esub> Y\<rparr>
      post_receive n Y (\<lambda>y. A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> \<Q> y) \<parallel> (B \<triangleright>\<^sup>\<infinity> y. (A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> \<Q> y)) \<guillemotleft> suffix n"
      using repeated_receive_transition .
    then have "
      A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> B \<triangleright>\<^sup>\<infinity> y. (A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> \<Q> y)
      \<rightarrow>\<^sub>s\<lparr>B \<triangleright>\<^bsub>n\<^esub> Y\<rparr>
      (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n \<parallel>
      post_receive n Y (\<lambda>y. A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> \<Q> y) \<parallel> (B \<triangleright>\<^sup>\<infinity> y. (A \<triangleright>\<^sup>\<infinity> x. \<P> x \<parallel> \<Q> y)) \<guillemotleft> suffix n"
      by (fact synchronous_transition.parallel_right_io)
    then show ?thesis
      unfolding
        post_receive_after_parallel
      and
        \<open>\<alpha> = IO \<eta> B' n Y\<close> and \<open>S = (A \<triangleright>\<^sup>\<infinity> x. \<P> x) \<guillemotleft> suffix n \<parallel> R\<close>
      and
        \<open>\<eta> = Receiving\<close> and \<open>B' = B\<close> and \<open>R = post_receive n Y \<Q> \<parallel> (B \<triangleright>\<^sup>\<infinity> y. \<Q> y) \<guillemotleft> suffix n\<close>
      using
        with_inner_repeated_receive_post_right_receive
      and
        right_amended_double_suffix_adapted [symmetric]
      and
        composition_in_universe
          [OF suffix_adapted_mutation_in_universe parallel_mutation_in_universe]
      by (intro exI conjI, use in assumption) (fastforce intro: rev_bexI)
  qed (blast elim: transition_from_repeated_receive)+
qed respectful

end

(*FIXME:
  Simplify the proof of the following lemma once #231 is resolved.

  In particular, do the following:

    \<^item> Turn the detailed proofs that involve
      \<^theory_text>\<open>repeated_receive_is_quasi_compatible_with_synchronous_bisimilarity\<close> into single-step proofs
      that use the \<^theory_text>\<open>bisimilarity\<close> proof method.

    \<^item> Merge the resulting proofs with adjacent proofs if \<^theory_text>\<open>bisimilarity\<close> can solve the whole step.

    \<^item> Merge applications of \<^theory_text>\<open>parallel_commutativity\<close> and \<^theory_text>\<open>parallel_associativity\<close> when possible.

    \<^item> Get rid of applications of compatibility rules whenever \<^theory_text>\<open>bisimilarity\<close> can be used instead.
*)
lemma inner_general_parallel_redundancy:
  fixes \<Q> :: "val \<Rightarrow> process family"
  assumes "\<And>x \<Q> :: val \<Rightarrow> process family. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> y. (\<P> x \<parallel> \<Q> y) \<sim>\<^sub>s \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> y. \<Q> y"
  shows "\<Parallel>x \<leftarrow> xs. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> y. (\<Parallel>x \<leftarrow> xs. \<P> x \<parallel> \<Q> y) \<sim>\<^sub>s \<Parallel>x \<leftarrow> xs. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> y. \<Q> y"
proof (induction xs arbitrary: \<Q>)
  case Nil
  have "post_receive n X (\<lambda>x. \<zero> \<parallel> \<Q> x) \<sim>\<^sub>s post_receive n X \<Q>" for n and X
  proof -
    have "(\<lambda>e. ((\<zero> \<parallel> \<Q> (X e)) \<guillemotleft> suffix n) e) = (\<lambda>e. (\<zero> \<guillemotleft> suffix n \<parallel> \<Q> (X e) \<guillemotleft> suffix n) e)"
      by (simp only: adapted_after_parallel)
    also have "\<dots> = \<zero> \<guillemotleft> suffix n \<parallel> (\<lambda>e. (\<Q> (X e) \<guillemotleft> suffix n) e)"
      by (subst environment_dependent_parallel) (fact refl)
    also have "\<dots> \<sim>\<^sub>s (\<lambda>e. (\<Q> (X e) \<guillemotleft> suffix n) e)"
      unfolding adapted_after_stop
      using parallel_left_identity .
    finally show ?thesis
      unfolding post_receive_def .
  qed
  then show ?case
    unfolding general_parallel.simps(1)
    by
      (intro
        synchronous.parallel_is_right_compatible_with_bisimilarity
        synchronous.repeated_receive_is_quasi_compatible_with_bisimilarity
      )
      simp
next
  case (Cons x xs \<Q>)
  have "
    post_receive n X (\<lambda>y. (\<P> x \<parallel> \<Parallel>x \<leftarrow> xs. \<P> x) \<parallel> \<Q> y)
    \<sim>\<^sub>s
    post_receive n X (\<lambda>y. \<Parallel>x \<leftarrow> xs. \<P> x \<parallel> (\<P> x \<parallel> \<Q> y))"
    for n and X
  proof -
    have "
      (\<lambda>e. (((\<P> x \<parallel> \<Parallel>x \<leftarrow> xs. \<P> x) \<parallel> \<Q> (X e)) \<guillemotleft> suffix n) e)
      =
      (\<lambda>e. ((\<P> x \<guillemotleft> suffix n \<parallel> (\<Parallel>x \<leftarrow> xs. \<P> x) \<guillemotleft> suffix n) \<parallel> \<Q> (X e) \<guillemotleft> suffix n) e)"
      by (simp only: adapted_after_parallel)
    also have "\<dots> = (\<P> x \<guillemotleft> suffix n \<parallel> (\<Parallel>x \<leftarrow> xs. \<P> x) \<guillemotleft> suffix n) \<parallel> (\<lambda>e. (\<Q> (X e) \<guillemotleft> suffix n) e)"
      by (subst environment_dependent_parallel) (fact refl)
    also have "\<dots> \<sim>\<^sub>s ((\<Parallel>x \<leftarrow> xs. \<P> x) \<guillemotleft> suffix n \<parallel> \<P> x \<guillemotleft> suffix n) \<parallel> (\<lambda>e. (\<Q> (X e) \<guillemotleft> suffix n) e)"
      by (intro synchronous.parallel_is_left_compatible_with_bisimilarity parallel_commutativity)
    also have "\<dots> \<sim>\<^sub>s (\<Parallel>x \<leftarrow> xs. \<P> x) \<guillemotleft> suffix n \<parallel> (\<P> x \<guillemotleft> suffix n \<parallel> (\<lambda>e. (\<Q> (X e) \<guillemotleft> suffix n) e))"
      using parallel_associativity .
    also have "\<dots> = (\<lambda>e. ((\<Parallel>x \<leftarrow> xs. \<P> x) \<guillemotleft> suffix n \<parallel> (\<P> x \<guillemotleft> suffix n \<parallel> \<Q> (X e) \<guillemotleft> suffix n)) e)"
      by
        (subst (3) environment_dependent_parallel, subst (4) environment_dependent_parallel)
        (fact refl)
    also have "\<dots> = (\<lambda>e. ((\<Parallel>x \<leftarrow> xs. \<P> x \<parallel> (\<P> x \<parallel> \<Q> (X e))) \<guillemotleft> suffix n) e)"
      by (simp only: adapted_after_parallel)
    finally show ?thesis
      unfolding post_receive_def .
  qed
  then have "
    (\<P> x \<parallel> \<Parallel>x \<leftarrow> xs. \<P> x) \<parallel> A \<triangleright>\<^sup>\<infinity> y. ((\<P> x \<parallel> \<Parallel>x \<leftarrow> xs. \<P> x) \<parallel> \<Q> y)
    \<sim>\<^sub>s
    (\<P> x \<parallel> \<Parallel>x \<leftarrow> xs. \<P> x) \<parallel> A \<triangleright>\<^sup>\<infinity> y. (\<Parallel>x \<leftarrow> xs. \<P> x \<parallel> (\<P> x \<parallel> \<Q> y))"
    by
      (intro
        synchronous.parallel_is_right_compatible_with_bisimilarity
        synchronous.repeated_receive_is_quasi_compatible_with_bisimilarity
      )
      simp
  also have "\<dots> \<sim>\<^sub>s \<P> x \<parallel> (\<Parallel>x \<leftarrow> xs. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> y. (\<Parallel>x \<leftarrow> xs. \<P> x \<parallel> (\<P> x \<parallel> \<Q> y)))"
    using parallel_associativity .
  also have "\<dots> \<sim>\<^sub>s \<P> x \<parallel> (\<Parallel>x \<leftarrow> xs. \<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> y. (\<P> x \<parallel> \<Q> y))"
    using Cons.IH
    by (rule synchronous.parallel_is_right_compatible_with_bisimilarity)
  also have "\<dots> \<sim>\<^sub>s \<Parallel>x \<leftarrow> xs. \<P> x \<parallel> (\<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> y. (\<P> x \<parallel> \<Q> y))"
    using parallel_left_commutativity .
  also have "\<dots> \<sim>\<^sub>s \<Parallel>x \<leftarrow> xs. \<P> x \<parallel> (\<P> x \<parallel> A \<triangleright>\<^sup>\<infinity> y. \<Q> y)"
    using assms
    by (rule synchronous.parallel_is_right_compatible_with_bisimilarity)
  also have "\<dots> \<sim>\<^sub>s (\<P> x \<parallel> \<Parallel>x \<leftarrow> xs. \<P> x) \<parallel> A \<triangleright>\<^sup>\<infinity> y. \<Q> y"
    using thorn_simps
    by equivalence
  finally show ?case
    unfolding general_parallel.simps(2) .
qed

(*FIXME:
  \<^item> Change the variable names in the statement of \<^theory_text>\<open>communication_with_rightmost_adjustment\<close>.

  \<^item> Make \<^theory_text>\<open>communication_with_rightmost_adjustment\<close> public.

  \<^item> Make \<^theory_text>\<open>communication_with_rightmost_adjustment\<close> conform with \<^theory_text>\<open>parallel_left_scope_extension\<close>.

  \<^item> Prove a right variant and use it in the proof of \<^theory_text>\<open>parallel_left_commutativity\<close> (swap the use
    and non-use of \<^theory_text>\<open>THEN synchronous.bisimilarity_symmetry_rule\<close>.
*)

(* FIXME:
  \<^item> The preservation lemmas should be separated from the \<^theory_text>\<open>lift_definition\<close> declarations, and such
    lemmas for \<^theory_text>\<open>injectively_adapted\<close> should be added (such lemmas for \<^theory_text>\<open>remove_adapted\<close> are already
    present.

  \<^item> If we need an extra proof method for invoking \<^theory_text>\<open>new_channel_scope_extension\<close>, we should not
    have tagged versions of other facts involving \<open>\<nu>\<close> and perhaps not even the \<^method>\<open>equivalence\<close>
    setup for tagged \<open>\<nu>\<close>.

  \<^item> Regarding rules formerly labeled ``homogenous'':

      \<^item> Add analogs of \<^theory_text>\<open>homogeneous_process_family_uncurry(1-3)\<close> that work with \<^theory_text>\<open>deep_uncurry\<close>.

      \<^item> Check that these analogs yield to proper behavior for channel and value arguments.

      \<^item> Add a configurable list of facts that is supposed to contain analogous rules for derived
        constructs like \<open>\<leftrightarrow>\<close>.

  \<^item> Possibly add \<^theory_text>\<open>homogeneous_process_family_uncurry(1-3)\<close> to make \<open>\<nabla>\<close>-elimination also work for
    processes that contain the respective constructions.

    Then we must make the transfer rules also work with types other than \<open>process\<close>. We might want to
    declare these rules only locally as transfer rules.

  \<^item> Implement \<^theory_text>\<open>bisimilarity\<close> such that \<open>remove\<close>s are pushed inwards in the conclusion after the
    rules have been applied (or concurrently, by adding the ``pushing inwards'' rules as additional
    rewrite rules for \<^theory_text>\<open>equivalence\<close>)

      \<^item> This should allow \<^theory_text>\<open>bisimilarity\<close> to work with the parallel scope extension rules and rules
        that are not universally quantified over process families or process family functions (like
        the rules of \<^theory_text>\<open>Communication\<close>)

      \<^item> Check if we still need specialized versions of the parallel scope extension rules for the
        case with less dependencies

  \<^item> Add a method \<^theory_text>\<open>scope_redundancy\<close> that does not push \<open>remove\<close>s inwards but pulls them outwards in
    the conclusion after the actual \<^theory_text>\<open>scope_redundancy\<close> rules has been applied.

  \<^item> To prevent our transferring from accidentally transferring to the quotient type, thus preventing
    relaxation in \<^theory_text>\<open>equivalence\<close>, we could perhaps temporarily wrap the bisimilarity relation.
*)

end
