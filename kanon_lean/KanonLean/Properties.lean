import Base
import KanonLean.Funs

open Primitives Result

namespace kanon

-- Need to remove the upper limit on the heartbeat number,
-- as otherwise `scalar_decr_tac` chokes.
set_option maxHeartbeats 0

instance record_inhabited : Inhabited Record := Inhabited.mk ⟨U32.ofInt 0, U32.ofInt 0, U32.ofInt 0⟩

lemma tail_eq (h : α) (t₁ : List α) (t₂ : List α) :
  t₁ = t₂ -> h :: t₁ = h :: t₂ := by simp

lemma take_append
  [hα : Inhabited α]
  (n : ℕ)
  (l : List α)
  (h_l_ne_nil: ¬(l = List.nil))
  (h_n_g_zero : n > 0)
  (h_n_le_l_len: n <= l.length) :
  List.take n l = List.take (n - 1) l ++ [List.index l (n - 1)] := by
  cases l with
  | nil => contradiction
  | cons h t =>
      induction n with
      | zero => contradiction
      | succ n₁ ih =>
          cases Classical.em (n₁ > 0) with
          | inl _ =>
              have : n₁ <= t.length + 1 := by
                simp at h_n_le_l_len
                exact Nat.le_add_right_of_le h_n_le_l_len
              simp_all
              rw [List.append_cons, <-ih]
              apply tail_eq
              cases Classical.em (t = []) with
              | inl _ =>
                  simp_all
              | inr _ =>
                  apply take_append
                  repeat' assumption
          | inr _ => simp_all

lemma leq_add_1 (x y : ℤ) : (x < y + 1 -> x <= y) := by
  intro h
  exact (Int.add_le_add_iff_right 1).mp h

lemma filter_count_true
  {α: Type}
  [hα : Inhabited α]
  (c: Usize)
  (i: Usize)
  (l: alloc.vec.Vec α)
  (hi: i.val < l.length)
  (f: α -> Bool)
  (hft: f (l.val.index i.toNat) == true)
  (hc: (c: ℤ) = ↑(List.filter f (List.take i.toNat ↑l)).length) :
  (c: ℤ) + 1#usize = ↑(List.filter f (List.take ((i: ℤ) + 1#usize).toNat ↑l)).length := by
  cases l with
  | mk l_val _ =>
      cases l_val with
      | nil =>
          have : i.val >= 0 := by scalar_tac
          have : i.val < 0 := by scalar_tac
          simp_all [not_lt_of_ge]
      | cons h t =>
        rw [take_append]
        repeat' simp_all [leq_add_1]

lemma filter_count_false
  {α: Type}
  [hα : Inhabited α]
  (c: Usize)
  (i: Usize)
  (l: alloc.vec.Vec α)
  (hi: i.val < l.length)
  (f: α -> Bool)
  (hft: f (l.val.index i.toNat) == false)
  (hc: (c: ℤ) = ↑(List.filter f (List.take i.toNat ↑l)).length) :
  (c: ℤ) = ↑(List.filter f (List.take ((i: ℤ) + 1#usize).toNat ↑l)).length := by
  cases l with
  | mk l_val _ =>
      cases l_val with
      | nil =>
          have : i.val >= 0 := by scalar_tac
          have : i.val < 0 := by scalar_tac
          simp_all [not_lt_of_ge]
      | cons h t =>
        rw [take_append]
        repeat' simp_all [leq_add_1]

@[pspec]
theorem count_similar_rows_loop_spec
  (kanon_instance : KAnonymity)
  (row : Record)
  (n_similar : Usize)
  (i : Usize)
  (hi : i.val <= kanon_instance.data.length)
  (hin: n_similar.val <= i.val)
  (hn :
    n_similar.val = (
      kanon_instance.data
        |> List.take i.toNat
        |> List.filter (λ other_row => Record.is_similar row other_row == ok true)
        |> List.length)) :
  ∃ n,
    (KAnonymity.count_similar_rows_loop kanon_instance row n_similar i) = ok n
      ∧ n.val = (kanon_instance.data.val
        |> List.filter (λ other_row => Record.is_similar row other_row == ok true)
        |> List.length) := by
  rw [KAnonymity.count_similar_rows_loop]
  simp
  split
  . rename_i hil
    progress as ⟨_, hr⟩
    rw [Record.is_similar]
    split
    . simp
      split
      . progress as ⟨_, hn_similar₁⟩
        progress as ⟨_, hi₁⟩
        progress
        . simp
          rw [hi₁, hn_similar₁]
          subst hr
          exact
            filter_count_true
            n_similar i kanon_instance.data hil
            (fun other_row => row.is_similar other_row == ok true)
            (by
              simp
              rw [Record.is_similar]
              split
              repeat' simp_all
              repeat rfl)
            hn
        . assumption
      . progress as ⟨_, hi₁⟩
        progress
        . simp
          rw [hi₁]
          exact
            filter_count_false
            n_similar i kanon_instance.data hil
            (fun other_row => row.is_similar other_row == ok true)
            (by
              simp
              rw [Record.is_similar]
              subst hr
              split
              repeat' simp_all
              repeat rfl)
            hn
        . assumption
    . simp
      progress as ⟨_, hi₁⟩
      progress
      . simp
        rw [hi₁]
        exact
            filter_count_false
            n_similar i kanon_instance.data hil
            (fun other_row => row.is_similar other_row == ok true)
            (by
              simp
              rw [Record.is_similar]
              subst hr
              split
              repeat simp_all
              rfl)
            hn
      . assumption
  . simp_all
termination_by (kanon_instance.data.length - i.val).toNat
decreasing_by repeat scalar_decr_tac

@[pspec]
theorem count_similar_rows_spec
  (kanon_instance : KAnonymity)
  (row : Record) :
  ∃ n, KAnonymity.count_similar_rows kanon_instance row = ok n
      ∧ List.length
        (kanon_instance.data
          |> List.filter (λ other_row => (Record.is_similar row other_row) == ok true)) = n.val := by
  rw [KAnonymity.count_similar_rows]
  progress
  simp_all

lemma filter_filter_true
  {α: Type}
  [hα : Inhabited α]
  (c: alloc.vec.Vec α)
  (i: Usize)
  (l: alloc.vec.Vec α)
  (hi: i.val < l.length)
  (f: α -> Bool)
  (hft: f (l.val.index i.toNat) == true)
  (hc: (c: List α) = ↑(List.filter f (List.take i.toNat ↑l))) :
  (c: List α) ++ [l.val.index i.toNat] = ↑(List.filter f (List.take ((i: ℤ) + 1#usize).toNat ↑l)) := by
  cases l with
  | mk l_val _ =>
      cases l_val with
      | nil =>
          have : i.val >= 0 := by scalar_tac
          have : i.val < 0 := by scalar_tac
          simp_all [not_lt_of_ge]
      | cons h t =>
        rw [take_append]
        repeat' simp_all [leq_add_1]

lemma filter_filter_false
  {α: Type}
  [hα : Inhabited α]
  (c: alloc.vec.Vec α)
  (i: Usize)
  (l: alloc.vec.Vec α)
  (hi: i.val < l.length)
  (f: α -> Bool)
  (hft: f (l.val.index i.toNat) == false)
  (hc: (c: List α) = ↑(List.filter f (List.take i.toNat ↑l))) :
  (c: List α) = ↑(List.filter f (List.take ((i: ℤ) + 1#usize).toNat ↑l)) := by
  cases l with
  | mk l_val _ =>
      cases l_val with
      | nil =>
          have : i.val >= 0 := by scalar_tac
          have : i.val < 0 := by scalar_tac
          simp_all [not_lt_of_ge]
      | cons h t =>
        rw [take_append]
        repeat' simp_all [leq_add_1]

@[pspec]
theorem anonymize_loop_spec
  (kanon_instance: KAnonymity)
  (anonymized_data_i : alloc.vec.Vec Record)
  (i : Usize)
  (hi : i.val <= kanon_instance.data.length)
  (hid: anonymized_data_i.length <= i.val)
  (hd : anonymized_data_i = (
    kanon_instance.data
    |> List.take i.toNat
    |> List.filter (λ row => (
      kanon_instance.data.val
        |> List.filter (λ other_row ↦ Record.is_similar row other_row == ok true)
        |> List.length) >= kanon_instance.k.val))) :
  ∃ anonymized_data, KAnonymity.anonymize_loop kanon_instance anonymized_data_i i = ok anonymized_data
      ∧ anonymized_data = (
        kanon_instance.data
        |> List.filter (λ row => (
          kanon_instance.data.val
            |> List.filter (λ other_row ↦ Record.is_similar row other_row == ok true)
            |> List.length) >= kanon_instance.k.val)) := by
  rw [KAnonymity.anonymize_loop]
  simp
  split
  . rename_i hil
    progress as ⟨r, hr⟩
    rw [ClonekanonRecord.clone]
    simp
    progress as ⟨n, hn⟩
    split
    . progress as ⟨anonymized_data_i₁, hanonymized_data_i₁⟩
      . progress as ⟨i₁, hi₁⟩
        progress
        . subst hr
          simp_all
        . simp
          rw [hi₁, hanonymized_data_i₁]
          subst hr
          exact
            filter_filter_true
            anonymized_data_i i kanon_instance.data hil
            (fun row => decide (kanon_instance.k.val ≤ ↑(List.filter
              (fun other_row => row.is_similar other_row == ok true) ↑kanon_instance.data).length))
            (by simp_all)
            hd
        . assumption
    . progress as ⟨i₁, hi₁⟩
      progress
      . simp
        rw [hi₁]
        subst hr
        exact
          filter_filter_false
          anonymized_data_i i kanon_instance.data hil
          (fun row => decide (kanon_instance.k.val ≤ ↑(List.filter
            (fun other_row => row.is_similar other_row == ok true) ↑kanon_instance.data).length))
          (by simp_all)
          hd
      . assumption
  . simp_all
termination_by (kanon_instance.data.length - i.val).toNat
decreasing_by repeat scalar_decr_tac

@[pspec]
theorem anonymize_spec
  (kanon_instance: KAnonymity) :
  ∃ anonymized_data, KAnonymity.anonymize kanon_instance = ok anonymized_data
      ∧ anonymized_data = (
        kanon_instance.data
        |> List.filter (λ row => (
          kanon_instance.data.val
            |> List.filter (λ other_row ↦ Record.is_similar row other_row == ok true)
            |> List.length) >= kanon_instance.k.val)) := by
  rw [KAnonymity.anonymize]
  progress
  simp_all

end kanon
