module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib

@[expose] public section

/-!
# Sieve / Foundations / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## WeightedBlockSieve -/

section

/- Native4.34.1 port of the preserved complete weighted block-sieve proof.
The historical source is retained byte-for-byte in the delta evidence. -/
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
namespace Green64Analytic.SieveContinuation
open scoped BigOperators

theorem weighted_block_sieve : ∀ {Ω : Type} (h J : ℕ) (blocks : Fin J → Finset ℕ) (z C η : ℝ)
(objects : Finset Ω) (w : Ω → ℝ) (bad : Ω → Finset ℕ) (g r : ℕ → ℝ) (X : ℝ),
1 < z → 2 ≤ h → Even h → 0 ≤ C → 0 < η → 0 ≤ X →
(∀ x ∈ objects, 0 ≤ w x) →
(∀ j p, p ∈ blocks j → Nat.Prime p ∧ z ^ ((1/2:ℝ)^(j.val+1)) < (p:ℝ) ∧ (p:ℝ) ≤ z ^ ((1/2:ℝ)^j.val)) →
(∀ j p, p ∈ blocks j → 0 ≤ g p ∧ g p ≤ 1-η) →
(∀ j, (∑ p ∈ blocks j, g p) ≤ C) →
let P := Finset.univ.biUnion blocks;
(∀ s ⊆ P, (∑ x ∈ objects, w x * ∏ p ∈ s, if p ∈ bad x then (1:ℝ) else 0) =
    X * (∏ p ∈ s, g p) + r (∏ p ∈ s, p)) →
let V := ∏ p ∈ P, (1-g p);
let ρ := ((Real.exp (Real.exp 1*C)/(1-Real.exp (-1)))/Real.exp (-C/η))*Real.exp (-(h:ℝ));
let D := z^(4*(h:ℝ)+2);
let E := ∑ d ∈ ((∏ p ∈ P, p).divisors.filter (fun d : ℕ => Squarefree d ∧ (d:ℝ) ≤ D)), |r d|;
let S := ∑ x ∈ objects, w x * (if ∀ j, blocks j ∩ bad x = ∅ then (1:ℝ) else 0);
X*V*(1-ρ*Real.exp ρ)-E ≤ S ∧ S ≤ X*V*Real.exp ρ+E := by
  have dis : ∀ (J : ℕ) (blocks : Fin J → Finset ℕ) (z : ℝ), 1 < z →
(∀ j p, p ∈ blocks j → z ^ ((1/2:ℝ)^(j.val+1)) < (p:ℝ) ∧ (p:ℝ) ≤ z ^ ((1/2:ℝ)^j.val)) →
∀ i j, i ≠ j → Disjoint (blocks i) (blocks j) := by
    intro J blocks z hz hp
    have hpow : ∀ m n : ℕ, m ≤ n → (1/2:ℝ)^n ≤ (1/2:ℝ)^m := by
      intro m n hmn
      obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
      rw [pow_add]
      have hk : (1/2:ℝ)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      simpa using mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ (1/2:ℝ)^m)
    have hd : ∀ i j : Fin J, i.val < j.val → Disjoint (blocks i) (blocks j) := by
      intro i j hij
      apply Finset.disjoint_left.mpr
      intro p hpi hpj
      have he := Real.rpow_le_rpow_of_exponent_le hz.le (hpow (i.val+1) j.val (by omega))
      have h1 := (hp i p hpi).1
      have h2 := (hp j p hpj).2
      linarith
    intro i j hij
    have hv : i.val ≠ j.val := fun he => hij (Fin.ext he)
    rcases lt_or_gt_of_ne hv with h | h
    · exact hd i j h
    · exact (hd j i h).symm
  have expb : ∀ {α : Type} [DecidableEq α] (h J : ℕ) (blocks : Fin J → Finset α) (g : α → ℝ) (C η : ℝ),
0 ≤ C → 0 < η → 1 ≤ h → Even h →
(∀ j p, p ∈ blocks j → 0 ≤ g p ∧ g p ≤ 1-η) →
(∀ j, (∑ p ∈ blocks j, g p) ≤ C) →
let a := fun j => ∏ p ∈ blocks j, (1-g p);
let u := fun j => ∑ n ∈ Finset.range ((j.val+1)*h+1), (-1:ℝ)^n * ∑ d ∈ (blocks j).powersetCard n, ∏ p ∈ d, g p;
let e := fun j => ∑ d ∈ (blocks j).powersetCard ((j.val+1)*h+1), ∏ p ∈ d, g p;
let A := ∏ j, a j;
let U := ∏ j, u j;
let E := ∑ j, e j * ∏ i ∈ Finset.univ.erase j, u i;
let ρ := ((Real.exp (Real.exp 1*C)/(1-Real.exp (-1)))/Real.exp (-C/η))*Real.exp (-(h:ℝ));
0 ≤ A ∧ 0 ≤ ρ ∧ U ≤ A*Real.exp ρ ∧ A*(1-ρ*Real.exp ρ) ≤ U-E := by
    have bonf : ∀ {α : Type} [DecidableEq α] (s : Finset α) (g : α → ℝ) (k : ℕ), (∀ p ∈ s, 0 ≤ g p ∧ g p ≤ 1) → Even k → let A := ∏ p ∈ s, (1-g p); let U := ∑ a ∈ Finset.range (k+1), (-1 : ℝ)^a * (∑ d ∈ s.powersetCard a, ∏ p ∈ d, g p); let E := ∑ d ∈ s.powersetCard (k+1), ∏ p ∈ d, g p; A ≤ U ∧ U-A ≤ E := by
      classical
      have rb : ∀ {α : Type} [Fintype α] [DecidableEq α] (s : Finset α) (g : α → ℝ) (k : ℕ), (∀ p, 0 ≤ g p ∧ g p ≤ 1) → Even k → let A := ∏ p ∈ s, (1-g p); let U := ∑ a ∈ Finset.range (k+1), (-1 : ℝ)^a * (∑ d ∈ s.powersetCard a, ∏ p ∈ d, g p); let E := ∑ d ∈ s.powersetCard (k+1), ∏ p ∈ d, g p; A ≤ U ∧ U-A ≤ E := by
        have countB : ∀ (t k : ℕ), Even k → let U : ℝ := ∑ a ∈ Finset.range (k + 1), (-1 : ℝ)^a * (t.choose a : ℝ); let I : ℝ := if t = 0 then 1 else 0; I ≤ U ∧ U - I ≤ (t.choose (k+1) : ℝ) := by
          intro t k hk
          dsimp
          cases t with
          | zero => simp [Finset.sum_range_succ']
          | succ n =>
            have hh := Int.alternating_sum_range_choose_eq_choose (n := n) (m := k)
            have hr : (∑ a ∈ Finset.range (k+1), (-1 : ℝ)^a * ((n+1).choose a : ℝ)) = (-1 : ℝ)^k * (n.choose k : ℝ) := by
              exact_mod_cast hh
            rw [hr, hk.neg_one_pow]
            simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, one_mul, sub_zero]
            constructor
            · positivity
            · exact_mod_cast (show n.choose k ≤ (n+1).choose (k+1) by rw [Nat.choose_succ_succ]; omega)
        have boolE : ∀ {α : Type} [DecidableEq α] (s B : Finset α) (k : ℕ), (∑ d ∈ s.powersetCard k, ∏ p ∈ d, (if p ∈ B then (1 : ℝ) else 0)) = ((s ∩ B).card.choose k : ℝ) := by
          intro α inst s B k
          have hb : ∀ d : Finset α, (∏ p ∈ d, (if p ∈ B then (1 : ℝ) else 0)) = if d ⊆ B then 1 else 0 := by
            intro d
            by_cases hd : d ⊆ B
            · simp [hd, Finset.prod_eq_one (fun p hp => if_pos (hd hp))]
            · rw [if_neg hd]
              have hex : ∃ p ∈ d, p ∉ B := by simpa [Finset.subset_iff] using hd
              obtain ⟨p,hp,hpb⟩ := hex
              exact Finset.prod_eq_zero hp (by simp [hpb])
          simp_rw [hb]
          rw [← Finset.sum_filter]
          have he : (s.powersetCard k).filter (fun d => d ⊆ B) = (s ∩ B).powersetCard k := by
            ext d
            simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_inter_iff]
            tauto
          rw [he]
          simp
        have boolA : ∀ {α : Type} [DecidableEq α] (s B : Finset α), (∏ p ∈ s, (if p ∈ B then (0 : ℝ) else 1)) = if (s ∩ B).card = 0 then 1 else 0 := by
          intro α inst s B
          by_cases h : (s ∩ B).card = 0
          · rw [if_pos h]
            apply Finset.prod_eq_one
            intro p hp
            apply if_neg
            intro hpb
            have hm : p ∈ s ∩ B := Finset.mem_inter.mpr ⟨hp,hpb⟩
            rw [Finset.card_eq_zero.mp h] at hm
            exact Finset.notMem_empty p hm
          · rw [if_neg h]
            obtain ⟨p,hp⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
            exact Finset.prod_eq_zero (Finset.mem_inter.mp hp).1 (if_pos (Finset.mem_inter.mp hp).2)
        have bern : ∀ {α : Type} [Fintype α] [DecidableEq α] (s : Finset α) (g : α → ℝ) (f : α → Bool → ℝ), (∑ b : α → Bool, (∏ p, (if b p then g p else 1-g p)) * (∏ p ∈ s, f p (b p))) = ∏ p ∈ s, ((1-g p) * f p false + g p * f p true) := by
          have bern : ∀ {α : Type} [Fintype α] [DecidableEq α] (g : α → ℝ) (f : α → Bool → ℝ), (∑ b : α → Bool, (∏ p, (if b p then g p else 1-g p)) * (∏ p, f p (b p))) = ∏ p, ((1-g p) * f p false + g p * f p true) := by
            intro α instF instD g f
            simp_rw [← Finset.prod_mul_distrib]
            rw [← Fintype.prod_sum (fun p (b : Bool) => (if b then g p else 1-g p) * f p b)]
            apply Finset.prod_congr rfl
            intro p hp
            simp [add_comm]
          have restrictP : ∀ {α : Type} [Fintype α] [DecidableEq α] (s : Finset α) (a : α → ℝ), (∏ p, if p ∈ s then a p else 1) = ∏ p ∈ s, a p := by
            intro α instF instD s a
            calc
              _ = ∏ p ∈ s, if p ∈ s then a p else 1 := (Finset.prod_subset (Finset.subset_univ s) (by intro p hp hps; simp [hps])).symm
              _ = _ := Finset.prod_congr rfl (fun p hp => if_pos hp)
          intro α instF instD s g f
          have h := bern g (fun p b => if p ∈ s then f p b else 1)
          simp_rw [restrictP] at h
          calc
            _ = ∏ p, ((1-g p) * (if p ∈ s then f p false else 1) + g p * (if p ∈ s then f p true else 1)) := h
            _ = ∏ p, if p ∈ s then ((1-g p) * f p false + g p * f p true) else 1 := by
              apply Finset.prod_congr rfl
              intro p hp
              by_cases hps : p ∈ s <;> simp [hps]
            _ = _ := restrictP _ _
        intro α instF instD s g k hg hk
        let w : (α → Bool) → ℝ := fun b => ∏ p, if b p then g p else 1-g p
        let es : ℕ → (α → Bool) → ℝ := fun n b => ∑ d ∈ s.powersetCard n, ∏ p ∈ d, if b p then (1:ℝ) else 0
        let av : (α → Bool) → ℝ := fun b => ∏ p ∈ s, if b p then (0:ℝ) else 1
        let up : (α → Bool) → ℝ := fun b => ∑ a ∈ Finset.range (k+1), (-1:ℝ)^a * es a b
        have hw : ∀ b, 0 ≤ w b := by
          intro b
          apply Finset.prod_nonneg
          intro p hp
          split_ifs
          · exact (hg p).1
          · exact sub_nonneg.mpr (hg p).2
        have hbool : ∀ b, av b ≤ up b ∧ up b - av b ≤ es (k+1) b := by
          intro b
          let B := Finset.univ.filter (fun p => b p = true)
          have hc := countB (s ∩ B).card k hk
          have hes : ∀ n, es n b = ((s ∩ B).card.choose n : ℝ) := by
            intro n
            simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using boolE s B n
          have hav : av b = if (s ∩ B).card = 0 then 1 else 0 := by
            simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using boolA s B
          simpa only [up, hes, hav] using hc
        have he : ∀ n, (∑ b, w b * es n b) = ∑ d ∈ s.powersetCard n, ∏ p ∈ d, g p := by
          intro n
          simp only [es, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro d hd
          simpa only [Bool.false_eq_true, if_false, if_true, mul_zero, mul_one, zero_add] using bern d g (fun _ b => if b then (1:ℝ) else 0)
        have ha : (∑ b, w b * av b) = ∏ p ∈ s, (1-g p) := by
          simpa only [Bool.false_eq_true, if_false, if_true, mul_zero, mul_one, add_zero] using bern s g (fun _ b => if b then (0:ℝ) else 1)
        have hu : (∑ b, w b * up b) = ∑ a ∈ Finset.range (k+1), (-1:ℝ)^a * (∑ d ∈ s.powersetCard a, ∏ p ∈ d, g p) := by
          simp only [up, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a ha
          simp_rw [mul_left_comm (w _) ((-1:ℝ)^a), ← Finset.mul_sum, he]
        have h1 := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (α → Bool))) => mul_le_mul_of_nonneg_left (hbool b).1 (hw b))
        have h2 := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (α → Bool))) => mul_le_mul_of_nonneg_left (hbool b).2 (hw b))
        simp only [mul_sub, Finset.sum_sub_distrib, ha, hu, he] at h1 h2
        exact ⟨h1,h2⟩
      have mapES : ∀ {α β : Type} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (s : Finset α) (g : β → ℝ) (n : ℕ), (∑ d ∈ (s.map f).powersetCard n, ∏ p ∈ d, g p) = ∑ d ∈ s.powersetCard n, ∏ p ∈ d, g (f p) := by
       intro α β _ _ f s g n
       rw [Finset.powersetCard_map, Finset.sum_map]
       apply Finset.sum_congr rfl
       intro d hd
       change (∏ p ∈ d.map f, g p) = _
       exact Finset.prod_map d f g
      intro α _ s g k hg hk
      let emb : ↥s ↪ α := ⟨Subtype.val, Subtype.val_injective⟩
      have he : s.attach.map emb = s := by ext p; simp [emb]
      have hm (n : ℕ) : (∑ d ∈ s.powersetCard n, ∏ p ∈ d, g p) =
          ∑ d ∈ s.attach.powersetCard n, ∏ p ∈ d, g p.val := by
        simpa only [he, emb, Function.Embedding.coeFn_mk] using mapES emb s.attach g n
      have hh := rb s.attach (fun p : ↥s => g p.val) k (fun p => hg p.val p.property) hk
      dsimp only at hh ⊢
      have hp : (∏ p ∈ s.attach, (1-g p.val)) = ∏ p ∈ s, (1-g p) := by
        simpa only [he, emb, Function.Embedding.coeFn_mk] using
          (Finset.prod_map s.attach emb (fun p => 1-g p)).symm
      simpa only [hm, hp] using hh
    have alow : ∀ {α : Type} (s : Finset α) (g : α → ℝ) (η C : ℝ), 0 < η → (∀ p ∈ s, 0 ≤ g p ∧ g p ≤ 1-η) → (∑ p ∈ s, g p) ≤ C → Real.exp (-C/η) ≤ ∏ p ∈ s, (1-g p) := by
      intro α s g η C hη hg hsum
      have hp : ∀ p ∈ s, 0 < 1-g p := fun p hp => by have := hg p hp; linarith
      have hlog : ∀ p ∈ s, -(g p)/η ≤ Real.log (1-g p) := by
        intro p hps
        have hgp := hg p hps
        have h1 := Real.one_sub_inv_le_log_of_pos (hp p hps)
        have he : 1 - (1-g p)⁻¹ = -(g p)/(1-g p) := by field_simp [ne_of_gt (hp p hps)]; ring
        rw [he] at h1
        have hd : g p / (1-g p) ≤ g p / η := div_le_div_of_nonneg_left hgp.1 hη (by linarith)
        simp only [neg_div] at h1 ⊢
        linarith
      have hl : -C/η ≤ ∑ p ∈ s, Real.log (1-g p) := by
        calc
          -C/η ≤ -(∑ p ∈ s, g p)/η := div_le_div_of_nonneg_right (neg_le_neg hsum) hη.le
          _ = ∑ p ∈ s, -(g p)/η := by simp only [← Finset.sum_div, ← Finset.sum_neg_distrib]
          _ ≤ _ := Finset.sum_le_sum hlog
      have he := Real.exp_le_exp.mpr hl
      rw [Real.exp_sum] at he
      exact he.trans_eq (Finset.prod_congr rfl (fun p hps => Real.exp_log (hp p hps)))
    have fac : ∀ {α : Type} [DecidableEq α] (s : Finset α) (g : α → ℝ), (∀ p ∈ s, 0 ≤ g p) → ∀ n : ℕ, (n.factorial : ℝ) * (∑ d ∈ s.powersetCard n, ∏ p ∈ d, g p) ≤ (∑ p ∈ s, g p)^n := by
      have recE : ∀ {α : Type} [DecidableEq α] (s : Finset α) (a : α) (g : α → ℝ) (n : ℕ), a ∉ s → (∑ d ∈ (insert a s).powersetCard (n+1), ∏ p ∈ d, g p) = (∑ d ∈ s.powersetCard (n+1), ∏ p ∈ d, g p) + g a * (∑ d ∈ s.powersetCard n, ∏ p ∈ d, g p) := by
        intro α inst s a g n ha
        have hnot : ∀ m, ∀ d ∈ s.powersetCard m, a ∉ d := fun m d hd h => ha ((Finset.mem_powersetCard.mp hd).1 h)
        rw [Finset.powersetCard_succ_insert ha n, Finset.sum_union]
        · congr 1
          rw [Finset.sum_image]
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro d hd
            rw [Finset.prod_insert (hnot n d hd)]
          · intro d hd e he hde
            have hh := congrArg (fun t : Finset α => t.erase a) hde
            simpa [Finset.erase_insert (hnot n d hd), Finset.erase_insert (hnot n e he)] using hh
        · apply Finset.disjoint_left.mpr
          intro d hd he
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp he
          exact hnot (n+1) (insert a e) hd (Finset.mem_insert_self a e)
      have twoTerm : ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → ∀ n : ℕ, a^(n+1) + (n+1 : ℕ) * b * a^n ≤ (a+b)^(n+1) := by
        intro a b ha hb n
        induction n with
        | zero => simp
        | succ n ih =>
          have hm := mul_le_mul_of_nonneg_right ih (add_nonneg ha hb)
          have hp : 0 ≤ (n+1 : ℝ) * b^2 * a^n := by positivity
          simp only [Nat.cast_add, Nat.cast_one] at *
          rw [pow_succ (a+b) (n+1)]
          rw [pow_succ a (n+1), pow_succ a n]
          rw [pow_succ a n] at hm
          nlinarith
      intro α inst s g hg
      induction s using Finset.induction_on with
      | empty =>
        intro n
        cases n with
        | zero => simp
        | succ n =>
          have he : (∅ : Finset α).powersetCard (n+1) = ∅ := by
            ext d
            simp [Finset.mem_powersetCard]
            rintro rfl
            simp
          simp [he]
      | @insert a s ha ih =>
        intro n
        have hga : 0 ≤ g a := hg a (Finset.mem_insert_self a s)
        have hgs : ∀ p ∈ s, 0 ≤ g p := fun p hp => hg p (Finset.mem_insert_of_mem hp)
        have hsum : 0 ≤ ∑ p ∈ s, g p := Finset.sum_nonneg hgs
        cases n with
        | zero => simp
        | succ n =>
          rw [recE s a g n ha, Finset.sum_insert ha]
          have h1 := ih hgs (n+1)
          have h2 := mul_le_mul_of_nonneg_left (ih hgs n) (mul_nonneg (show (0 : ℝ) ≤ (n+1 : ℕ) by positivity) hga)
          have h3 := twoTerm (∑ p ∈ s, g p) (g a) hsum hga n
          simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at *
          rw [add_comm (g a)]
          nlinarith
    have tail : ∀ (C : ℝ), 0 ≤ C → ∀ (h J : ℕ), 1 ≤ h → (∑ j ∈ Finset.range J, C^((j+1)*h+1) / (((j+1)*h+1).factorial : ℝ)) ≤ (Real.exp (Real.exp 1 * C) / (1-Real.exp (-1))) * Real.exp (-(h : ℝ)) := by
      have decay : ∀ (C : ℝ), 0 ≤ C → ∀ n : ℕ, C^n / (n.factorial : ℝ) ≤ Real.exp (Real.exp 1 * C) * Real.exp (-(n : ℝ)) := by
        intro C hC n
        have h := Real.pow_div_factorial_le_exp (Real.exp 1 * C) (mul_nonneg (le_of_lt (Real.exp_pos 1)) hC) n
        rw [mul_pow, ← Real.exp_nat_mul, mul_one] at h
        rw [Real.exp_neg, ← div_eq_mul_inv]
        apply (le_div_iff₀ (Real.exp_pos _)).mpr
        calc
          C^n / (n.factorial : ℝ) * Real.exp (n : ℝ) = Real.exp (n : ℝ) * C^n / (n.factorial : ℝ) := by ring
          _ ≤ _ := h
      have geom : ∀ (q : ℝ), 0 ≤ q → q < 1 → ∀ N : ℕ, (∑ j ∈ Finset.range N, q^j) ≤ 1/(1-q) := by
        intro q hq hq1 N
        have he : (∑ j ∈ Finset.range N, q^j) * (1-q) = 1-q^N := by
          induction N with
          | zero => simp
          | succ N ih => rw [Finset.sum_range_succ, pow_succ]; nlinarith
        apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
        nlinarith [pow_nonneg hq N]
      intro C hC h J hh
      have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
      have hq : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
      have hq1 : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
      have point : ∀ j : ℕ, Real.exp (-(((j+1)*h+1 : ℕ) : ℝ)) ≤ Real.exp (-(h : ℝ)) * (Real.exp (-1))^j := by
        intro j
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        push_cast
        have hm := mul_le_mul_of_nonneg_left hhR (show (0 : ℝ) ≤ j by positivity)
        nlinarith
      calc
        _ ≤ ∑ j ∈ Finset.range J, Real.exp (Real.exp 1 * C) * (Real.exp (-(h:ℝ)) * (Real.exp (-1))^j) := by
          apply Finset.sum_le_sum
          intro j hj
          exact (decay C hC _).trans (mul_le_mul_of_nonneg_left (point j) (Real.exp_pos _).le)
        _ = (Real.exp (Real.exp 1 * C) * Real.exp (-(h:ℝ))) * (∑ j ∈ Finset.range J, (Real.exp (-1))^j) := by simp only [← mul_assoc, Finset.mul_sum]
        _ ≤ (Real.exp (Real.exp 1 * C) * Real.exp (-(h:ℝ))) * (1/(1-Real.exp (-1))) := mul_le_mul_of_nonneg_left (geom _ hq hq1 J) (by positivity)
        _ = _ := by ring
    have bb : ∀ {ι : Type} [DecidableEq ι] (J : Finset ι) (a u e : ι → ℝ), (∀ j ∈ J, 0 < a j ∧ a j ≤ u j ∧ u j ≤ a j + e j) → let R := ∑ j ∈ J, e j / a j; (∏ j ∈ J, a j) ≤ (∏ j ∈ J, u j) ∧ (∏ j ∈ J, u j) ≤ (∏ j ∈ J, a j) * Real.exp R ∧ (∑ j ∈ J, e j * ∏ i ∈ J.erase j, u i) ≤ (∏ j ∈ J, a j) * R * Real.exp R := by
      intro ι inst J a u e h
      dsimp only
      have ha : ∀ j ∈ J, 0 ≤ a j := fun j hj => (h j hj).1.le
      have hu : ∀ j ∈ J, 0 ≤ u j := fun j hj => (ha j hj).trans (h j hj).2.1
      have he : ∀ j ∈ J, 0 ≤ e j := by intro j hj; have := h j hj; linarith
      have hr : ∀ j ∈ J, 0 ≤ e j / a j := fun j hj => div_nonneg (he j hj) (ha j hj)
      have upper : (∏ j ∈ J, u j) ≤ (∏ j ∈ J, a j) * Real.exp (∑ j ∈ J, e j / a j) := by
        calc
          _ ≤ ∏ j ∈ J, a j * Real.exp (e j / a j) := by
            apply Finset.prod_le_prod₀ hu
            intro j hj
            have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (e j/a j)) (ha j hj)
            have hx : a j * (e j/a j + 1) = a j + e j := by field_simp [ne_of_gt (h j hj).1]; ring
            rw [hx] at hh
            exact (h j hj).2.2.trans hh
          _ = _ := by rw [Finset.prod_mul_distrib, Real.exp_sum]
      refine ⟨Finset.prod_le_prod₀ ha (fun j hj => (h j hj).2.1), upper, ?_⟩
      calc
        _ ≤ ∑ j ∈ J, (e j / a j) * ((∏ i ∈ J, a i) * Real.exp (∑ i ∈ J, e i/a i)) := by
          apply Finset.sum_le_sum
          intro j hj
          have hp : 0 ≤ ∏ i ∈ J.erase j, u i := Finset.prod_nonneg (fun i hi => hu i (Finset.mem_of_mem_erase hi))
          have ht : a j * (∏ i ∈ J.erase j, u i) ≤ ∏ i ∈ J, u i := by
            rw [← Finset.mul_prod_erase J u hj]
            exact mul_le_mul_of_nonneg_right (h j hj).2.1 hp
          calc
            _ = (e j/a j) * (a j * ∏ i ∈ J.erase j, u i) := by field_simp [ne_of_gt (h j hj).1]
            _ ≤ (e j/a j) * (∏ i ∈ J, u i) := mul_le_mul_of_nonneg_left ht (hr j hj)
            _ ≤ _ := mul_le_mul_of_nonneg_left upper (hr j hj)
        _ = _ := by rw [← Finset.sum_mul]; ring
    classical
    intro α _ h J blocks g C η hC hη hh hev hg hs
    dsimp only
    let a := fun j => ∏ p ∈ blocks j, (1-g p)
    let u := fun j => ∑ n ∈ Finset.range ((j.val+1)*h+1), (-1:ℝ)^n * ∑ d ∈ (blocks j).powersetCard n, ∏ p ∈ d, g p
    let e := fun j => ∑ d ∈ (blocks j).powersetCard ((j.val+1)*h+1), ∏ p ∈ d, g p
    let A := ∏ j, a j
    let R := ∑ j, e j/a j
    let ρ := ((Real.exp (Real.exp 1*C)/(1-Real.exp (-1)))/Real.exp (-C/η))*Real.exp (-(h:ℝ))
    have ha : ∀ j, Real.exp (-C/η) ≤ a j := fun j => alow (blocks j) g η C hη (hg j) (hs j)
    have hap : ∀ j, 0 < a j := fun j => (Real.exp_pos _).trans_le (ha j)
    have hen : ∀ j, 0 ≤ e j := by
      intro j
      exact Finset.sum_nonneg (fun d hd => Finset.prod_nonneg (fun p hp =>
        (hg j p ((Finset.mem_powersetCard.mp hd).1 hp)).1))
    have heb : ∀ j, e j ≤ C^((j.val+1)*h+1)/(((j.val+1)*h+1).factorial:ℝ) := by
      intro j
      apply (le_div_iff₀ (by positivity : (0:ℝ) < (((j.val+1)*h+1).factorial:ℝ))).mpr
      have h1 := fac (blocks j) g (fun p hp => (hg j p hp).1) ((j.val+1)*h+1)
      have h2 := pow_le_pow_left₀ (Finset.sum_nonneg (fun p hp => (hg j p hp).1)) (hs j) ((j.val+1)*h+1)
      dsimp [e]
      nlinarith
    have hR : R ≤ ρ := by
      calc
        R ≤ ∑ j : Fin J, (C^((j.val+1)*h+1)/(((j.val+1)*h+1).factorial:ℝ))/Real.exp (-C/η) := by
          apply Finset.sum_le_sum
          intro j hj
          exact (div_le_div_of_nonneg_left (hen j) (Real.exp_pos _) (ha j)).trans
            (div_le_div_of_nonneg_right (heb j) (Real.exp_pos _).le)
        _ = (∑ j ∈ Finset.range J, C^((j+1)*h+1)/(((j+1)*h+1).factorial:ℝ))/Real.exp (-C/η) := by
          rw [← Finset.sum_div, ← Fin.sum_univ_eq_sum_range]
        _ ≤ ((Real.exp (Real.exp 1*C)/(1-Real.exp (-1)))*Real.exp (-(h:ℝ)))/Real.exp (-C/η) :=
          div_le_div_of_nonneg_right (tail C hC h J hh) (Real.exp_pos _).le
        _ = ρ := by dsimp [ρ]; ring
    have hRn : 0 ≤ R := Finset.sum_nonneg (fun j _ => div_nonneg (hen j) (hap j).le)
    have hρ : 0 ≤ ρ := hRn.trans hR
    have hA : 0 ≤ A := Finset.prod_nonneg (fun j _ => (hap j).le)
    have hlocal : ∀ j ∈ (Finset.univ : Finset (Fin J)), 0 < a j ∧ a j ≤ u j ∧ u j ≤ a j+e j := by
      intro j hj
      have hb := bonf (blocks j) g ((j.val+1)*h)
        (fun p hp => ⟨(hg j p hp).1, (hg j p hp).2.trans (by linarith)⟩)
        (hev.mul_left (j.val+1))
      exact ⟨hap j, hb.1, by dsimp [a,u,e]; linarith [hb.2]⟩
    have hb := bb Finset.univ a u e hlocal
    have hexp := Real.exp_le_exp.mpr hR
    have hmul : R*Real.exp R ≤ ρ*Real.exp ρ :=
      mul_le_mul hR hexp (Real.exp_pos _).le hρ
    change 0 ≤ A ∧ 0 ≤ ρ ∧ (∏ j, u j) ≤ A*Real.exp ρ ∧
      A*(1-ρ*Real.exp ρ) ≤ (∏ j, u j)-(∑ j, e j*∏ i ∈ Finset.univ.erase j, u i)
    refine ⟨hA,hρ,hb.2.1.trans (mul_le_mul_of_nonneg_left hexp hA),?_⟩
    have hh1 := mul_le_mul_of_nonneg_left hmul hA
    dsimp only at hb
    dsimp [A,R] at hh1
    nlinarith [hb.1,hb.2.2]
  have poly : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (blocks : ι → Finset ℕ) (k : ι → ℕ),
(∀ i j, i ≠ j → Disjoint (blocks i) (blocks j)) →
let choices := fun i => ↥((blocks i).powerset);
let a : ∀ i, choices i → ℝ := fun i t => if t.val.card ≤ k i then (-1:ℝ)^t.val.card else 0;
let e : ∀ i, choices i → ℝ := fun i t => if t.val.card = k i+1 then 1 else 0;
let cu := fun f : (∀ i, choices i) => ∏ i, a i (f i);
let cc := fun f : (∀ i, choices i) => ∑ j, e j (f j) * ∏ i ∈ Finset.univ.erase j, a i (f i);
∀ g : ℕ → ℝ,
let mon := fun f : (∀ i, choices i) => ∏ p ∈ Finset.univ.biUnion (fun i => (f i).val), g p;
let u := fun j => ∑ n ∈ Finset.range (k j+1), (-1:ℝ)^n * ∑ d ∈ (blocks j).powersetCard n, ∏ p ∈ d, g p;
let e' := fun j => ∑ d ∈ (blocks j).powersetCard (k j+1), ∏ p ∈ d, g p;
(∏ j, u j) = ∑ f, cu f*mon f ∧
(∏ j, u j)-(∑ j, e' j*∏ i ∈ Finset.univ.erase j, u i) = ∑ f, (cu f-cc f)*mon f := by
    have poly : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (blocks : ι → Finset ℕ) (k : ι → ℕ), (∀ i j, i ≠ j → Disjoint (blocks i) (blocks j)) →
  let choices := fun i => ↥((blocks i).powerset);
  let a : ∀ i, choices i → ℝ := fun i t => if t.val.card ≤ k i then (-1:ℝ)^t.val.card else 0;
  let e : ∀ i, choices i → ℝ := fun i t => if t.val.card = k i + 1 then 1 else 0;
  let cu := fun f : (∀ i, choices i) => ∏ i, a i (f i);
  let cc := fun f : (∀ i, choices i) => ∑ j, e j (f j) * ∏ i ∈ Finset.univ.erase j, a i (f i);
  (∀ f, |cu f| ≤ 1 ∧ |cc f| ≤ 1 ∧ |cu f-cc f| ≤ 1) ∧
  ∀ g : ℕ → ℝ,
  let m : ∀ i, choices i → ℝ := fun i t => ∏ p ∈ t.val, g p;
  let mon := fun f : (∀ i, choices i) => ∏ p ∈ Finset.univ.biUnion (fun i => (f i).val), g p;
  let U := ∏ i, ∑ t, a i t * m i t;
  let C := ∑ j, (∑ t, e j t * m j t) * ∏ i ∈ Finset.univ.erase j, (∑ t, a i t * m i t);
  U = ∑ f, cu f * mon f ∧ C = ∑ f, cc f * mon f ∧ U-C = ∑ f, (cu f-cc f) * mon f := by
      classical
      have expandU : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (κ : ι → Type) [∀ i, Fintype (κ i)] (a m : ∀ i, κ i → ℝ), (∏ i, ∑ t, a i t * m i t) = ∑ f : (∀ i, κ i), (∏ i, a i (f i)) * (∏ i, m i (f i)) := by
        intros
        rw [Fintype.prod_sum]
        simp only [Finset.prod_mul_distrib]
      have expandC : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (κ : ι → Type) [∀ i, Fintype (κ i)] (a e m : ∀ i, κ i → ℝ), (∑ j, (∑ t, e j t * m j t) * ∏ i ∈ Finset.univ.erase j, (∑ t, a i t * m i t)) = ∑ f : (∀ i, κ i), (∑ j, e j (f j) * ∏ i ∈ Finset.univ.erase j, a i (f i)) * (∏ i, m i (f i)) := by
        have selectP : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a e : ι → ℝ) (j : ι), (∏ i, if i = j then e i else a i) = e j * ∏ i ∈ Finset.univ.erase j, a i := by
          intro ι instF instD a e j
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
          simp only [ite_true]
          congr 1
          apply Finset.prod_congr rfl
          intro i hi
          exact if_neg (Finset.mem_erase.mp hi).1
        have expandP : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (κ : ι → Type) [∀ i, Fintype (κ i)] (a m : ∀ i, κ i → ℝ), (∏ i, ∑ t, a i t * m i t) = ∑ f : (∀ i, κ i), (∏ i, a i (f i)) * (∏ i, m i (f i)) := by
          intros
          rw [Fintype.prod_sum]
          simp only [Finset.prod_mul_distrib]
        intro ι instF instD κ instK a e m
        calc
          _ = ∑ j, ∏ i, (∑ t, (if i = j then e i t else a i t) * m i t) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [← selectP (fun i => ∑ t, a i t * m i t) (fun i => ∑ t, e i t * m i t) j]
            apply Finset.prod_congr rfl
            intro i hi
            by_cases hij : i = j <;> simp [hij]
          _ = ∑ j, ∑ f : (∀ i, κ i), (∏ i, (if i = j then e i (f i) else a i (f i))) * (∏ i, m i (f i)) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact expandP κ (fun i t => if i = j then e i t else a i t) m
          _ = _ := by
            rw [Finset.sum_comm]
            simp_rw [selectP, Finset.sum_mul]
      have coeffBound : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (degree k : ι → ℕ), let v := fun i => if degree i ≤ k i then (-1 : ℝ)^(degree i) else 0; let e := fun i => if degree i = k i + 1 then (1 : ℝ) else 0; let u := ∏ i, v i; let c := ∑ j, e j * ∏ i ∈ Finset.univ.erase j, v i; |u| ≤ 1 ∧ |c| ≤ 1 ∧ |u-c| ≤ 1 := by
        classical
        intro ι instF instD degree k
        dsimp only
        let v : ι → ℝ := fun i => if degree i ≤ k i then (-1 : ℝ)^degree i else 0
        let e : ι → ℝ := fun i => if degree i = k i + 1 then 1 else 0
        have hv : ∀ i, |v i| ≤ 1 := by intro i; dsimp [v]; split_ifs <;> simp
        have hp : ∀ s : Finset ι, |∏ i ∈ s, v i| ≤ 1 := by
          intro s
          rw [Finset.abs_prod]
          exact Finset.prod_le_one₀ (fun i hi => abs_nonneg _) (fun i hi => hv i)
        refine ⟨hp _, ?_⟩
        by_cases hall : ∀ i, degree i ≤ k i
        · have he : ∀ i, e i = 0 := by intro i; dsimp [e]; exact if_neg (by have := hall i; omega)
          simp only [show ∀ i, (if degree i = k i + 1 then (1:ℝ) else 0) = 0 from he, zero_mul, Finset.sum_const_zero, abs_zero, zero_le_one, sub_zero, true_and]
          exact hp _
        · obtain ⟨j,hj⟩ := not_forall.mp hall
          have hvj : v j = 0 := if_neg hj
          have hu : (∏ i, v i) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hvj
          have hother : ∀ l, l ≠ j → e l * (∏ i ∈ Finset.univ.erase l, v i) = 0 := by
            intro l hlj
            have hz : (∏ i ∈ Finset.univ.erase l, v i) = 0 := Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hlj.symm, Finset.mem_univ j⟩) hvj
            rw [hz, mul_zero]
          have hc : (∑ l, e l * ∏ i ∈ Finset.univ.erase l, v i) = e j * ∏ i ∈ Finset.univ.erase j, v i := Finset.sum_eq_single j (fun l hl hlj => hother l hlj) (by simp)
          have hb : |e j * ∏ i ∈ Finset.univ.erase j, v i| ≤ 1 := by
            dsimp [e]
            split_ifs <;> simp only [one_mul, zero_mul, abs_zero, zero_le_one]
            exact hp _
          change |∑ l, e l * ∏ i ∈ Finset.univ.erase l, v i| ≤ 1 ∧ |(∏ i, v i) - ∑ l, e l * ∏ i ∈ Finset.univ.erase l, v i| ≤ 1
          rw [hc, hu]
          simpa using And.intro hb hb
      intro ι instF instD blocks k hdis
      dsimp only
      constructor
      · intro f
        exact coeffBound (fun i => (f i).val.card) k
      · intro g
        have hmon : ∀ f : (∀ i, ↥((blocks i).powerset)), (∏ i, ∏ p ∈ (f i).val, g p) = ∏ p ∈ Finset.univ.biUnion (fun i => (f i).val), g p := by
          intro f
          symm
          apply Finset.prod_biUnion
          intro i hi j hj hij
          exact (hdis i j hij).mono (Finset.mem_powerset.mp (f i).property) (Finset.mem_powerset.mp (f j).property)
        have hu := expandU (fun i => ↥((blocks i).powerset)) (fun i t => if t.val.card ≤ k i then (-1:ℝ)^t.val.card else 0) (fun i t => ∏ p ∈ t.val, g p)
        have hc := expandC (fun i => ↥((blocks i).powerset)) (fun i t => if t.val.card ≤ k i then (-1:ℝ)^t.val.card else 0) (fun i t => if t.val.card = k i+1 then 1 else 0) (fun i t => ∏ p ∈ t.val, g p)
        simp_rw [hmon] at hu hc
        refine ⟨hu,hc,?_⟩
        rw [hu,hc,← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro f hf
        ring
    have bridge : ∀ {α : Type} [DecidableEq α] (s : Finset α) (k : ℕ) (f : Finset α → ℝ), (∑ t : ↥(s.powerset), (if t.val.card ≤ k then (-1:ℝ)^t.val.card else 0) * f t.val) = (∑ a ∈ Finset.range (k+1), (-1:ℝ)^a * ∑ d ∈ s.powersetCard a, f d) ∧ (∑ t : ↥(s.powerset), (if t.val.card = k+1 then (1:ℝ) else 0) * f t.val) = ∑ d ∈ s.powersetCard (k+1), f d := by
      have trunc : ∀ {α : Type} [DecidableEq α] (s : Finset α) (k : ℕ) (f : Finset α → ℝ), (∑ a ∈ Finset.range (k+1), (-1 : ℝ)^a * ∑ d ∈ s.powersetCard a, f d) = ∑ d ∈ s.powerset, if d.card ≤ k then (-1 : ℝ)^d.card * f d else 0 := by
        intro α inst s k f
        calc
          _ = ∑ a ∈ Finset.range (k+1), ∑ d ∈ s.powerset with d.card = a, (-1 : ℝ)^d.card * f d := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.mul_sum, Finset.powersetCard_eq_filter]
            apply Finset.sum_congr rfl
            intro d hd
            rw [(Finset.mem_filter.mp hd).2]
          _ = ∑ d ∈ s.powerset with d.card ∈ Finset.range (k+1), (-1 : ℝ)^d.card * f d := Finset.sum_fiberwise_eq_sum_filter _ _ _ _
          _ = _ := by simp [Finset.sum_filter, Finset.mem_range, Nat.lt_succ_iff]
      intro α inst s k f
      constructor
      · rw [Finset.sum_coe_sort s.powerset (fun t => (if t.card ≤ k then (-1:ℝ)^t.card else 0) * f t)]
        simp only [ite_mul, zero_mul]
        exact (trunc s k f).symm
      · rw [Finset.sum_coe_sort s.powerset (fun t => (if t.card = k+1 then (1:ℝ) else 0) * f t)]
        simp only [ite_mul, one_mul, zero_mul]
        rw [← Finset.sum_filter, ← Finset.powersetCard_eq_filter]
    intro ι _ _ blocks k hdis
    dsimp only
    intro g
    have hp := (poly blocks k hdis).2 g
    dsimp only at hp
    have hU := fun j => (bridge (blocks j) (k j) (fun d => ∏ p ∈ d, g p)).1
    have hE := fun j => (bridge (blocks j) (k j) (fun d => ∏ p ∈ d, g p)).2
    simp_rw [hU, hE] at hp
    exact ⟨hp.1,hp.2.2⟩
  have rem : ∀ {Ω : Type} (h J : ℕ) (blocks : Fin J → Finset ℕ) (z : ℝ),
1 < z →
(∀ i j, i ≠ j → Disjoint (blocks i) (blocks j)) →
(∀ j p, p ∈ blocks j → Nat.Prime p ∧ (p:ℝ) ≤ z ^ ((1/2:ℝ)^j.val)) →
let P := Finset.univ.biUnion blocks;
∀ (objects : Finset Ω) (w : Ω → ℝ) (bad : Ω → Finset ℕ) (g r : ℕ → ℝ) (X : ℝ),
(∀ s ⊆ P, (∑ x ∈ objects, w x * ∏ p ∈ s, if p ∈ bad x then (1:ℝ) else 0) =
    X * (∏ p ∈ s, g p) + r (∏ p ∈ s, p)) →
let choices := fun j => ↥((blocks j).powerset);
let a : ∀ j, choices j → ℝ := fun j t => if t.val.card ≤ (j.val+1)*h then (-1:ℝ)^t.val.card else 0;
let e : ∀ j, choices j → ℝ := fun j t => if t.val.card = (j.val+1)*h+1 then 1 else 0;
let cu := fun f : (∀ j, choices j) => ∏ j, a j (f j);
let cc := fun f : (∀ j, choices j) => ∑ j, e j (f j) * ∏ i ∈ Finset.univ.erase j, a i (f i);
let F := fun f : (∀ j, choices j) => Finset.univ.biUnion (fun j => (f j).val);
let E := ∑ d ∈ (P.powerset.image (fun s => ∏ p ∈ s, p)).filter (fun d : ℕ => (d:ℝ) ≤ z^(4*(h:ℝ)+2)), |r d|;
∀ lower : Bool,
let c := fun f => if lower then cu f-cc f else cu f;
|(∑ x ∈ objects, w x * ∑ f, c f * ∏ p ∈ F f, if p ∈ bad x then (1:ℝ) else 0)
  - X * ∑ f, c f * ∏ p ∈ F f, g p| ≤ E := by
    have rem : ∀ {Ω D : Type} (objects : Finset Ω) (support : Finset D) (w : Ω → ℝ) (monomial : Ω → D → ℝ) (c g r : D → ℝ) (X : ℝ), (∀ d ∈ support, ∑ x ∈ objects, w x * monomial x d = X * g d + r d) → (∀ d ∈ support, |c d| ≤ 1) → |(∑ x ∈ objects, w x * ∑ d ∈ support, c d * monomial x d) - X * ∑ d ∈ support, c d * g d| ≤ ∑ d ∈ support with c d ≠ 0, |r d| := by
      intro Ω D objects support w monomial c g r X hcount hc
      have he : (∑ x ∈ objects, w x * ∑ d ∈ support, c d * monomial x d) - X * ∑ d ∈ support, c d * g d = ∑ d ∈ support, c d * r d := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        simp_rw [show ∀ x d, w x * (c d * monomial x d) = c d * (w x * monomial x d) by intros; ring]
        simp_rw [← Finset.mul_sum]
        rw [show X * (∑ d ∈ support, c d * g d) = ∑ d ∈ support, X * (c d * g d) by rw [Finset.mul_sum], ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro d hd
        rw [hcount d hd]
        ring
      rw [he]
      calc
        |∑ d ∈ support, c d * r d| ≤ ∑ d ∈ support, |c d * r d| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ support, if c d ≠ 0 then |r d| else 0 := by
          apply Finset.sum_le_sum
          intro d hd
          by_cases hz : c d = 0
          · simp [hz]
          · simp only [hz, ne_eq, not_false_eq_true, ite_true, abs_mul]
            exact (mul_le_mul_of_nonneg_right (hc d hd) (abs_nonneg (r d))).trans_eq (one_mul _)
        _ = _ := by rw [Finset.sum_filter]
    
    have coef : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (degree k : ι → ℕ), let v := fun i => if degree i ≤ k i then (-1 : ℝ)^(degree i) else 0; let e := fun i => if degree i = k i + 1 then (1 : ℝ) else 0; let u := ∏ i, v i; let c := ∑ j, e j * ∏ i ∈ Finset.univ.erase j, v i; |u| ≤ 1 ∧ |c| ≤ 1 ∧ |u-c| ≤ 1 := by
      classical
      intro ι instF instD degree k
      dsimp only
      let v : ι → ℝ := fun i => if degree i ≤ k i then (-1 : ℝ)^degree i else 0
      let e : ι → ℝ := fun i => if degree i = k i + 1 then 1 else 0
      have hv : ∀ i, |v i| ≤ 1 := by intro i; dsimp [v]; split_ifs <;> simp
      have hp : ∀ s : Finset ι, |∏ i ∈ s, v i| ≤ 1 := by
        intro s
        rw [Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun i hi => abs_nonneg _) (fun i hi => hv i)
      refine ⟨hp _, ?_⟩
      by_cases hall : ∀ i, degree i ≤ k i
      · have he : ∀ i, e i = 0 := by intro i; dsimp [e]; exact if_neg (by have := hall i; omega)
        simp only [show ∀ i, (if degree i = k i + 1 then (1:ℝ) else 0) = 0 from he, zero_mul, Finset.sum_const_zero, abs_zero, zero_le_one, sub_zero, true_and]
        exact hp _
      · obtain ⟨j,hj⟩ := not_forall.mp hall
        have hvj : v j = 0 := if_neg hj
        have hu : (∏ i, v i) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hvj
        have hother : ∀ l, l ≠ j → e l * (∏ i ∈ Finset.univ.erase l, v i) = 0 := by
          intro l hlj
          have hz : (∏ i ∈ Finset.univ.erase l, v i) = 0 := Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hlj.symm, Finset.mem_univ j⟩) hvj
          rw [hz, mul_zero]
        have hc : (∑ l, e l * ∏ i ∈ Finset.univ.erase l, v i) = e j * ∏ i ∈ Finset.univ.erase j, v i := Finset.sum_eq_single j (fun l hl hlj => hother l hlj) (by simp)
        have hb : |e j * ∏ i ∈ Finset.univ.erase j, v i| ≤ 1 := by
          dsimp [e]
          split_ifs <;> simp only [one_mul, zero_mul, abs_zero, zero_le_one]
          exact hp _
        change |∑ l, e l * ∏ i ∈ Finset.univ.erase l, v i| ≤ 1 ∧ |(∏ i, v i) - ∑ l, e l * ∏ i ∈ Finset.univ.erase l, v i| ≤ 1
        rw [hc, hu]
        simpa using And.intro hb hb
    have enc : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (blocks : ι → Finset ℕ), (∀ i j, i ≠ j → Disjoint (blocks i) (blocks j)) → (∀ i p, p ∈ blocks i → Nat.Prime p) → let encode := fun f : (∀ i, ↥((blocks i).powerset)) => ∏ p ∈ Finset.univ.biUnion (fun i => (f i).val), p; Function.Injective encode ∧ ∀ f, Squarefree (encode f) := by
      have unionInj : ∀ {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α] (blocks : ι → Finset α), (∀ i j, i ≠ j → Disjoint (blocks i) (blocks j)) → Function.Injective (fun f : (∀ i, ↥((blocks i).powerset)) => Finset.univ.biUnion (fun i => (f i).val)) := by
        intro ι α instF instI instA blocks hdis f g hfg
        have hsub : ∀ (a : ∀ i, ↥((blocks i).powerset)) i, (a i).val ⊆ blocks i := fun a i => Finset.mem_powerset.mp (a i).property
        have recover : ∀ (a : ∀ i, ↥((blocks i).powerset)) i, (Finset.univ.biUnion (fun j => (a j).val)) ∩ blocks i = (a i).val := by
          intro a i
          ext p
          constructor
          · intro hp
            obtain ⟨hj,hpi⟩ := Finset.mem_inter.mp hp
            obtain ⟨j, _, hpj⟩ := Finset.mem_biUnion.mp hj
            by_cases he : j = i
            · subst j; exact hpj
            · exact False.elim ((Finset.disjoint_left.mp (hdis j i he)) (hsub a j hpj) hpi)
          · intro hp
            exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hp⟩, hsub a i hp⟩
        funext i
        apply Subtype.ext
        rw [← recover f i, ← recover g i]
        exact congrArg (fun t : Finset α => t ∩ blocks i) hfg
      have primeInj : ∀ (s t : Finset ℕ), (∀ p ∈ s, Nat.Prime p) → (∀ p ∈ t, Nat.Prime p) → (∏ p ∈ s, p) = (∏ p ∈ t, p) → s = t := by
        have primeMem : ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) → ∀ q : ℕ, Nat.Prime q → (q ∣ ∏ p ∈ s, p ↔ q ∈ s) := by
          intro s hs q hq
          constructor
          · intro hd
            by_contra hn
            have hh : ¬ q ∣ ∏ p ∈ s, p := hq.prime.not_dvd_finset_prod (by
              intro p hp hqp
              rcases (Nat.dvd_prime (hs p hp)).mp hqp with h1 | he
              · exact hq.ne_one h1
              · exact hn (he.symm ▸ hp))
            exact hh hd
          · intro hqmem
            exact Finset.dvd_prod_of_mem (fun p : ℕ => p) hqmem
        intro s t hs ht hprod
        apply Finset.Subset.antisymm
        · intro p hp
          apply (primeMem t ht p (hs p hp)).mp
          rw [← hprod]
          exact (primeMem s hs p (hs p hp)).mpr hp
        · intro p hp
          apply (primeMem s hs p (ht p hp)).mp
          rw [hprod]
          exact (primeMem t ht p (ht p hp)).mpr hp
      have sqfree : ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) → Squarefree (∏ p ∈ s, p) := by
        have primeMem : ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) → ∀ q : ℕ, Nat.Prime q → (q ∣ ∏ p ∈ s, p ↔ q ∈ s) := by
          intro s hs q hq
          constructor
          · intro hd
            by_contra hn
            have hh : ¬ q ∣ ∏ p ∈ s, p := hq.prime.not_dvd_finset_prod (by
              intro p hp hqp
              rcases (Nat.dvd_prime (hs p hp)).mp hqp with h1 | he
              · exact hq.ne_one h1
              · exact hn (he.symm ▸ hp))
            exact hh hd
          · intro hqmem
            exact Finset.dvd_prod_of_mem (fun p : ℕ => p) hqmem
        intro s hs
        apply Nat.squarefree_iff_prime_squarefree.mpr
        intro q hq hqq
        have hqd : q ∣ ∏ p ∈ s, p := dvd_trans (dvd_mul_right q q) hqq
        have hqm : q ∈ s := (primeMem s hs q hq).mp hqd
        rw [← Finset.mul_prod_erase s (fun p : ℕ => p) hqm] at hqq
        have hd : q ∣ ∏ p ∈ s.erase q, p := (Nat.mul_dvd_mul_iff_left hq.pos).mp hqq
        have hm := (primeMem (s.erase q) (fun p hp => hs p (Finset.mem_of_mem_erase hp)) q hq).mp hd
        exact (Finset.notMem_erase q s) hm
      intro ι instF instD blocks hdis hprime
      dsimp only
      have hp : ∀ (f : ∀ i, ↥((blocks i).powerset)) p, p ∈ Finset.univ.biUnion (fun i => (f i).val) → Nat.Prime p := by
        intro f p hpf
        obtain ⟨i,_,hpi⟩ := Finset.mem_biUnion.mp hpf
        exact hprime i p ((Finset.mem_powerset.mp (f i).property) hpi)
      constructor
      · intro f g he
        apply unionInj blocks hdis
        exact primeInj _ _ (hp f) (hp g) he
      · intro f
        exact sqfree _ (hp f)
    have level : ∀ (h J : ℕ) (blocks : Fin J → Finset ℕ) (z : ℝ),
  1 < z →
  (∀ i j, i ≠ j → Disjoint (blocks i) (blocks j)) →
  (∀ j p, p ∈ blocks j → Nat.Prime p ∧ (p:ℝ) ≤ z ^ ((1/2:ℝ)^j.val)) →
  let choices := fun j => ↥((blocks j).powerset);
  let a : ∀ j, choices j → ℝ := fun j t => if t.val.card ≤ (j.val+1)*h then (-1:ℝ)^t.val.card else 0;
  let e : ∀ j, choices j → ℝ := fun j t => if t.val.card = (j.val+1)*h+1 then 1 else 0;
  let cu := fun f : (∀ j, choices j) => ∏ j, a j (f j);
  let cc := fun f : (∀ j, choices j) => ∑ j, e j (f j) * ∏ i ∈ Finset.univ.erase j, a i (f i);
  let encode := fun f : (∀ j, choices j) => ∏ p ∈ Finset.univ.biUnion (fun j => (f j).val), p;
  ∀ f, cu f ≠ 0 ∨ cu f-cc f ≠ 0 → Squarefree (encode f) ∧ (encode f:ℝ) ≤ z ^ (4*(h:ℝ)+2) := by
      have enc : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (blocks : ι → Finset ℕ), (∀ i j, i ≠ j → Disjoint (blocks i) (blocks j)) → (∀ i p, p ∈ blocks i → Nat.Prime p) → let encode := fun f : (∀ i, ↥((blocks i).powerset)) => ∏ p ∈ Finset.univ.biUnion (fun i => (f i).val), p; Function.Injective encode ∧ ∀ f, Squarefree (encode f) := by
        have unionInj : ∀ {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α] (blocks : ι → Finset α), (∀ i j, i ≠ j → Disjoint (blocks i) (blocks j)) → Function.Injective (fun f : (∀ i, ↥((blocks i).powerset)) => Finset.univ.biUnion (fun i => (f i).val)) := by
          intro ι α instF instI instA blocks hdis f g hfg
          have hsub : ∀ (a : ∀ i, ↥((blocks i).powerset)) i, (a i).val ⊆ blocks i := fun a i => Finset.mem_powerset.mp (a i).property
          have recover : ∀ (a : ∀ i, ↥((blocks i).powerset)) i, (Finset.univ.biUnion (fun j => (a j).val)) ∩ blocks i = (a i).val := by
            intro a i
            ext p
            constructor
            · intro hp
              obtain ⟨hj,hpi⟩ := Finset.mem_inter.mp hp
              obtain ⟨j, _, hpj⟩ := Finset.mem_biUnion.mp hj
              by_cases he : j = i
              · subst j; exact hpj
              · exact False.elim ((Finset.disjoint_left.mp (hdis j i he)) (hsub a j hpj) hpi)
            · intro hp
              exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hp⟩, hsub a i hp⟩
          funext i
          apply Subtype.ext
          rw [← recover f i, ← recover g i]
          exact congrArg (fun t : Finset α => t ∩ blocks i) hfg
        have primeInj : ∀ (s t : Finset ℕ), (∀ p ∈ s, Nat.Prime p) → (∀ p ∈ t, Nat.Prime p) → (∏ p ∈ s, p) = (∏ p ∈ t, p) → s = t := by
          have primeMem : ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) → ∀ q : ℕ, Nat.Prime q → (q ∣ ∏ p ∈ s, p ↔ q ∈ s) := by
            intro s hs q hq
            constructor
            · intro hd
              by_contra hn
              have hh : ¬ q ∣ ∏ p ∈ s, p := hq.prime.not_dvd_finset_prod (by
                intro p hp hqp
                rcases (Nat.dvd_prime (hs p hp)).mp hqp with h1 | he
                · exact hq.ne_one h1
                · exact hn (he.symm ▸ hp))
              exact hh hd
            · intro hqmem
              exact Finset.dvd_prod_of_mem (fun p : ℕ => p) hqmem
          intro s t hs ht hprod
          apply Finset.Subset.antisymm
          · intro p hp
            apply (primeMem t ht p (hs p hp)).mp
            rw [← hprod]
            exact (primeMem s hs p (hs p hp)).mpr hp
          · intro p hp
            apply (primeMem s hs p (ht p hp)).mp
            rw [hprod]
            exact (primeMem t ht p (ht p hp)).mpr hp
        have sqfree : ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) → Squarefree (∏ p ∈ s, p) := by
          have primeMem : ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) → ∀ q : ℕ, Nat.Prime q → (q ∣ ∏ p ∈ s, p ↔ q ∈ s) := by
            intro s hs q hq
            constructor
            · intro hd
              by_contra hn
              have hh : ¬ q ∣ ∏ p ∈ s, p := hq.prime.not_dvd_finset_prod (by
                intro p hp hqp
                rcases (Nat.dvd_prime (hs p hp)).mp hqp with h1 | he
                · exact hq.ne_one h1
                · exact hn (he.symm ▸ hp))
              exact hh hd
            · intro hqmem
              exact Finset.dvd_prod_of_mem (fun p : ℕ => p) hqmem
          intro s hs
          apply Nat.squarefree_iff_prime_squarefree.mpr
          intro q hq hqq
          have hqd : q ∣ ∏ p ∈ s, p := dvd_trans (dvd_mul_right q q) hqq
          have hqm : q ∈ s := (primeMem s hs q hq).mp hqd
          rw [← Finset.mul_prod_erase s (fun p : ℕ => p) hqm] at hqq
          have hd : q ∣ ∏ p ∈ s.erase q, p := (Nat.mul_dvd_mul_iff_left hq.pos).mp hqq
          have hm := (primeMem (s.erase q) (fun p hp => hs p (Finset.mem_of_mem_erase hp)) q hq).mp hd
          exact (Finset.notMem_erase q s) hm
        intro ι instF instD blocks hdis hprime
        dsimp only
        have hp : ∀ (f : ∀ i, ↥((blocks i).powerset)) p, p ∈ Finset.univ.biUnion (fun i => (f i).val) → Nat.Prime p := by
          intro f p hpf
          obtain ⟨i,_,hpi⟩ := Finset.mem_biUnion.mp hpf
          exact hprime i p ((Finset.mem_powerset.mp (f i).property) hpi)
        constructor
        · intro f g he
          apply unionInj blocks hdis
          exact primeInj _ _ (hp f) (hp g) he
        · intro f
          exact sqfree _ (hp f)
      have level : ∀ (h J : ℕ) (s : Fin J → Finset ℕ) (z : ℝ),
    1 < z →
    (∀ j p, p ∈ s j → 0 < p ∧ (p:ℝ) ≤ z ^ ((1/2:ℝ)^j.val)) →
    ((∀ j, (s j).card ≤ (j.val+1)*h) ∨
     (∃ r, (s r).card ≤ (r.val+1)*h+1 ∧ ∀ j, j ≠ r → (s j).card ≤ (j.val+1)*h)) →
    ((∏ j, ∏ p ∈ s j, p : ℕ):ℝ) ≤ z ^ (4*(h:ℝ)+2) := by
        have lp : ∀ {ι : Type} (s : Finset ι) (v e : ι → ℝ) (z : ℝ), 0 < z → (∀ i ∈ s, 0 < v i ∧ v i ≤ z ^ (e i)) → (∏ i ∈ s, v i) ≤ z ^ (∑ i ∈ s, e i) := by
          intro ι s v e z hz hv
          have hp : 0 < ∏ i ∈ s, v i := Finset.prod_pos (fun i hi => (hv i hi).1)
          apply (Real.log_le_log_iff hp (Real.rpow_pos_of_pos hz _)).mp
          rw [Real.log_prod (fun i hi => ne_of_gt (hv i hi).1), Real.log_rpow hz]
          calc
            (∑ i ∈ s, Real.log (v i)) ≤ ∑ i ∈ s, e i * Real.log z := by
              apply Finset.sum_le_sum
              intro i hi
              calc
                Real.log (v i) ≤ Real.log (z ^ e i) := Real.log_le_log (hv i hi).1 (hv i hi).2
                _ = _ := Real.log_rpow hz _
            _ = _ := by rw [Finset.sum_mul]
        have deg : ∀ (h J : ℕ) (degree : ℕ → ℕ),
      ((∀ j ∈ Finset.range J, degree j ≤ (j+1)*h) ∨
      (∃ r ∈ Finset.range J, degree r ≤ (r+1)*h+1 ∧ ∀ j ∈ Finset.range J, j ≠ r → degree j ≤ (j+1)*h)) →
      (∑ j ∈ Finset.range J, (degree j:ℝ)*(1/2:ℝ)^j) ≤ 4*(h:ℝ)+1 := by
          have geom : ∀ J : ℕ, (∑ j ∈ Finset.range J, ((j:ℝ)+1)*(1/2:ℝ)^j) ≤ 4 := by
            intro J
            have he : ∀ N : ℕ, (∑ j ∈ Finset.range N, ((j:ℝ)+1)*(1/2:ℝ)^j)+(2*(N:ℝ)+4)*(1/2:ℝ)^N = 4 := by
              intro N
              induction N with
              | zero => norm_num
              | succ N ih =>
                rw [Finset.sum_range_succ, pow_succ]
                push_cast
                nlinarith [ih]
            have hp : 0 ≤ (2*(J:ℝ)+4)*(1/2:ℝ)^J := by positivity
            linarith [he J]
          intro h J degree hadm
          have hg : (∑ j ∈ Finset.range J, (((j+1)*h:ℕ):ℝ)*(1/2:ℝ)^j) ≤ 4*(h:ℝ) := by
            calc
              _ = (h:ℝ)*(∑ j ∈ Finset.range J, ((j:ℝ)+1)*(1/2:ℝ)^j) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j hj
                push_cast
                ring
              _ ≤ (h:ℝ)*4 := mul_le_mul_of_nonneg_left (geom J) (Nat.cast_nonneg _)
              _ = _ := by ring
          rcases hadm with ha | ⟨r,hr,hrd,ho⟩
          · have hh : (∑ j ∈ Finset.range J, (degree j:ℝ)*(1/2:ℝ)^j) ≤ ∑ j ∈ Finset.range J, (((j+1)*h:ℕ):ℝ)*(1/2:ℝ)^j := by
              apply Finset.sum_le_sum
              intro j hj
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact_mod_cast ha j hj
            linarith
          · have hh : (∑ j ∈ Finset.range J, (degree j:ℝ)*(1/2:ℝ)^j) ≤ ∑ j ∈ Finset.range J, ((((j+1)*h:ℕ):ℝ)+(if j=r then 1 else 0))*(1/2:ℝ)^j := by
              apply Finset.sum_le_sum
              intro j hj
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              by_cases hjr : j=r
              · subst j
                simp only [ite_true]
                exact_mod_cast hrd
              · simp only [hjr,ite_false,add_zero]
                exact_mod_cast ho j hj hjr
            have he : (∑ j ∈ Finset.range J, ((((j+1)*h:ℕ):ℝ)+(if j=r then 1 else 0))*(1/2:ℝ)^j) =
                (∑ j ∈ Finset.range J, (((j+1)*h:ℕ):ℝ)*(1/2:ℝ)^j)+(1/2:ℝ)^r := by
              simp_rw [add_mul]
              rw [Finset.sum_add_distrib]
              congr 1
              simp [ite_mul, Finset.sum_ite_eq',hr]
            have hp : (1/2:ℝ)^r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
            rw [he] at hh
            linarith
        
        intro h J s z hz hs hadm
        let degree : ℕ → ℕ := fun j => if hj : j < J then (s ⟨j,hj⟩).card else 0
        have hadm' : (∀ j ∈ Finset.range J, degree j ≤ (j+1)*h) ∨
            (∃ r ∈ Finset.range J, degree r ≤ (r+1)*h+1 ∧
              ∀ j ∈ Finset.range J, j ≠ r → degree j ≤ (j+1)*h) := by
          rcases hadm with hh | ⟨r, hr, hh⟩
          · left; intro j hj; simpa [degree, Finset.mem_range.mp hj] using hh ⟨j,Finset.mem_range.mp hj⟩
          · right
            refine ⟨r.val, Finset.mem_range.mpr r.isLt, ?_, ?_⟩
            · simpa [degree, r.isLt] using hr
            · intro j hj hjr
              simpa [degree, Finset.mem_range.mp hj] using
                hh ⟨j,Finset.mem_range.mp hj⟩ (fun he => hjr (congrArg Fin.val he))
        have hd : (∑ j : Fin J, ((s j).card:ℝ)*(1/2:ℝ)^j.val) ≤ 4*(h:ℝ)+1 := by
          have he : (∑ j : Fin J, ((s j).card:ℝ)*(1/2:ℝ)^j.val) =
              ∑ j ∈ Finset.range J, (degree j:ℝ)*(1/2:ℝ)^j := by
            rw [← Fin.sum_univ_eq_sum_range]
            apply Finset.sum_congr rfl
            intro j hj
            simp [degree, j.isLt]
          rw [he]
          exact deg h J degree hadm'
        have hblock : ∀ j : Fin J, 0 < (∏ p ∈ s j, (p:ℝ)) ∧
            (∏ p ∈ s j, (p:ℝ)) ≤ z ^ (((s j).card:ℝ)*(1/2:ℝ)^j.val) := by
          intro j
          constructor
          · exact Finset.prod_pos (fun p hp => by exact_mod_cast (hs j p hp).1)
          · simpa using lp (s j) (fun p => (p:ℝ)) (fun _ => (1/2:ℝ)^j.val) z
              (by linarith) (fun p hp => ⟨by exact_mod_cast (hs j p hp).1, (hs j p hp).2⟩)
        push_cast
        exact (lp Finset.univ _ _ z (by linarith) (fun j _ => hblock j)).trans
          (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith))
      have profile : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (degree k : ι → ℕ),
    let v := fun i => if degree i ≤ k i then (-1:ℝ)^degree i else 0;
    let e := fun i => if degree i = k i+1 then (1:ℝ) else 0;
    let u := ∏ i, v i;
    let c := ∑ j, e j * ∏ i ∈ Finset.univ.erase j, v i;
    u ≠ 0 ∨ u-c ≠ 0 →
    (∀ i, degree i ≤ k i) ∨
    (∃ j, degree j = k j+1 ∧ ∀ i, i ≠ j → degree i ≤ k i) := by
        classical
        intro ι _ _ degree k
        dsimp only
        let v := fun i => if degree i ≤ k i then (-1:ℝ)^degree i else 0
        let e := fun i => if degree i = k i+1 then (1:ℝ) else 0
        change (∏ i, v i) ≠ 0 ∨ (∏ i, v i)-(∑ j, e j * ∏ i ∈ Finset.univ.erase j, v i) ≠ 0 → _
        intro hn
        by_cases hu : ∀ i, degree i ≤ k i
        · exact Or.inl hu
        right
        have hz : (∏ i, v i) = 0 := by
          obtain ⟨i, hi⟩ := not_forall.mp hu
          exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [v,hi])
        have hc : (∑ j, e j * ∏ i ∈ Finset.univ.erase j, v i) ≠ 0 := by
          rcases hn with hn | hn
          · exact (hn hz).elim
          · simpa [hz] using hn
        obtain ⟨j, hj, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
        have he : degree j = k j+1 := by
          by_contra hh
          exact hterm (by simp [e,hh])
        refine ⟨j,he,?_⟩
        intro i hij
        by_contra hh
        have hp : (∏ i ∈ Finset.univ.erase j, v i) = 0 :=
          Finset.prod_eq_zero (i := i) (by simp [hij]) (by simp [v,hh])
        exact hterm (by rw [hp,mul_zero])
      classical
      intro h J blocks z hz hdis hp
      dsimp only
      intro f hf
      have sub (j : Fin J) : (f j).val ⊆ blocks j := Finset.mem_powerset.mp (f j).property
      have hds : ∀ i ∈ (Finset.univ : Finset (Fin J)), ∀ j ∈ Finset.univ, i ≠ j →
          Disjoint (f i).val (f j).val :=
        fun i _ j _ hij => (hdis i j hij).mono (sub i) (sub j)
      constructor
      · exact (enc blocks hdis (fun j p hjp => (hp j p hjp).1)).2 f
      · have he : (∏ p ∈ Finset.univ.biUnion (fun j => (f j).val), p) =
            ∏ j, ∏ p ∈ (f j).val, p := Finset.prod_biUnion hds
        rw [he]
        apply level h J (fun j => (f j).val) z hz
        · intro j p hjp
          exact ⟨(hp j p (sub j hjp)).1.pos, (hp j p (sub j hjp)).2⟩
        · rcases profile (fun j => (f j).val.card) (fun j => (j.val+1)*h) hf with hh | ⟨r,hr,hh⟩
          · exact Or.inl hh
          · exact Or.inr ⟨r,hr.le,hh⟩
    classical
    intro Ω h J blocks z hz hdis hp
    dsimp only
    intro objects w bad g r X hcount
    intro lower
    let choices := fun j => ↥((blocks j).powerset)
    let a : ∀ j, choices j → ℝ := fun j t => if t.val.card ≤ (j.val+1)*h then (-1:ℝ)^t.val.card else 0
    let e : ∀ j, choices j → ℝ := fun j t => if t.val.card = (j.val+1)*h+1 then 1 else 0
    let cu := fun f : (∀ j, choices j) => ∏ j, a j (f j)
    let cc := fun f : (∀ j, choices j) => ∑ j, e j (f j) * ∏ i ∈ Finset.univ.erase j, a i (f i)
    let c := fun f => if lower then cu f-cc f else cu f
    let F := fun f : (∀ j, choices j) => Finset.univ.biUnion (fun j => (f j).val)
    let encode := fun f : (∀ j, choices j) => ∏ p ∈ F f, p
    let P := Finset.univ.biUnion blocks
    let T := (P.powerset.image (fun s => ∏ p ∈ s, p)).filter (fun d : ℕ => (d:ℝ) ≤ z^(4*(h:ℝ)+2))
    have hsub : ∀ f, F f ⊆ P := by
      intro f p hp
      obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
      exact Finset.mem_biUnion.mpr ⟨j,hj,(Finset.mem_powerset.mp (f j).property) hpj⟩
    have hc : ∀ f, |c f| ≤ 1 := by
      intro f
      have hh := coef (fun j => (f j).val.card) (fun j => (j.val+1)*h)
      cases lower
      · exact hh.1
      · exact hh.2.2
    have hb := rem objects Finset.univ w
      (fun x f => ∏ p ∈ F f, if p ∈ bad x then (1:ℝ) else 0)
      c (fun f => ∏ p ∈ F f, g p) (fun f => r (encode f)) X
      (fun f _ => hcount (F f) (hsub f)) (fun f _ => hc f)
    have hinj := (enc blocks hdis (fun j p hjp => (hp j p hjp).1)).1
    have hsu : (Finset.univ.filter (fun f => c f ≠ 0)).image encode ⊆ T := by
      intro d hd
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hd
      refine Finset.mem_filter.mpr ⟨?_,?_⟩
      · exact Finset.mem_image.mpr ⟨F f,Finset.mem_powerset.mpr (hsub f),rfl⟩
      · have hcn := (Finset.mem_filter.mp hf).2
        have hn : cu f ≠ 0 ∨ cu f-cc f ≠ 0 := by
          cases lower
          · exact Or.inl hcn
          · exact Or.inr hcn
        exact (level h J blocks z hz hdis hp f hn).2
    have he : (∑ f ∈ Finset.univ.filter (fun f => c f ≠ 0), |r (encode f)|) =
        ∑ d ∈ (Finset.univ.filter (fun f => c f ≠ 0)).image encode, |r d| := by
      rw [Finset.sum_image]
      intro f hf t ht he
      exact hinj he
    exact hb.trans (he.trans_le (Finset.sum_le_sum_of_subset_of_nonneg hsu (fun d _ _ => abs_nonneg _)))
  have divs : ∀ (P : Finset ℕ), (∀ p ∈ P, Nat.Prime p) → ∀ s ⊆ P,
(∏ p ∈ s, p) ∈ (∏ p ∈ P, p).divisors ∧ Squarefree (∏ p ∈ s, p) := by
    have sf : ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) → Squarefree (∏ p ∈ s, p) := by
      have primeMem : ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) → ∀ q : ℕ, Nat.Prime q → (q ∣ ∏ p ∈ s, p ↔ q ∈ s) := by
        intro s hs q hq
        constructor
        · intro hd
          by_contra hn
          have hh : ¬ q ∣ ∏ p ∈ s, p := hq.prime.not_dvd_finset_prod (by
            intro p hp hqp
            rcases (Nat.dvd_prime (hs p hp)).mp hqp with h1 | he
            · exact hq.ne_one h1
            · exact hn (he.symm ▸ hp))
          exact hh hd
        · intro hqmem
          exact Finset.dvd_prod_of_mem (fun p : ℕ => p) hqmem
      intro s hs
      apply Nat.squarefree_iff_prime_squarefree.mpr
      intro q hq hqq
      have hqd : q ∣ ∏ p ∈ s, p := dvd_trans (dvd_mul_right q q) hqq
      have hqm : q ∈ s := (primeMem s hs q hq).mp hqd
      rw [← Finset.mul_prod_erase s (fun p : ℕ => p) hqm] at hqq
      have hd : q ∣ ∏ p ∈ s.erase q, p := (Nat.mul_dvd_mul_iff_left hq.pos).mp hqq
      have hm := (primeMem (s.erase q) (fun p hp => hs p (Finset.mem_of_mem_erase hp)) q hq).mp hd
      exact (Finset.notMem_erase q s) hm
    intro P hp s hs
    refine ⟨?_,sf s (fun p hps => hp p (hs hps))⟩
    apply Nat.mem_divisors.mpr
    constructor
    · exact Finset.prod_dvd_prod_of_subset s P (fun p => p) hs
    · exact ne_of_gt (Finset.prod_pos (fun p hpp => (hp p hpp).pos))
  have sand : ∀ {Ω ι α : Type} [DecidableEq ι] [DecidableEq α] (objects : Finset Ω) (w : Ω → ℝ) (bad : Ω → Finset α) (J : Finset ι) (blocks : ι → Finset α) (k : ι → ℕ),
(∀ x ∈ objects, 0 ≤ w x) → (∀ j ∈ J, Even (k j)) →
let U := fun x j => ∑ a ∈ Finset.range (k j+1), (-1:ℝ)^a * ∑ d ∈ (blocks j).powersetCard a, ∏ p ∈ d, if p ∈ bad x then (1:ℝ) else 0;
let E := fun x j => ∑ d ∈ (blocks j).powersetCard (k j+1), ∏ p ∈ d, if p ∈ bad x then (1:ℝ) else 0;
let I := fun x => if ∀ j ∈ J, blocks j ∩ bad x = ∅ then (1:ℝ) else 0;
(∑ x ∈ objects, w x*((∏ j ∈ J, U x j)-(∑ j ∈ J, E x j * ∏ i ∈ J.erase j, U x i))) ≤ ∑ x ∈ objects, w x*I x ∧
(∑ x ∈ objects, w x*I x) ≤ ∑ x ∈ objects, w x*(∏ j ∈ J, U x j) := by
    have sandwich : ∀ {ι α : Type} [DecidableEq ι] [DecidableEq α] (J : Finset ι) (blocks : ι → Finset α) (B : Finset α) (k : ι → ℕ), (∀ j ∈ J, Even (k j)) → let U := fun j => ∑ a ∈ Finset.range (k j + 1), (-1 : ℝ)^a * ∑ d ∈ (blocks j).powersetCard a, ∏ p ∈ d, (if p ∈ B then (1 : ℝ) else 0); let E := fun j => ∑ d ∈ (blocks j).powersetCard (k j + 1), ∏ p ∈ d, (if p ∈ B then (1 : ℝ) else 0); let avoid : ℝ := if ∀ j ∈ J, blocks j ∩ B = ∅ then 1 else 0; (∏ j ∈ J, U j) - (∑ j ∈ J, E j * ∏ i ∈ J.erase j, U i) ≤ avoid ∧ avoid ≤ ∏ j ∈ J, U j := by
      classical
      have countBound : ∀ (t k : ℕ), Even k → let U : ℝ := ∑ a ∈ Finset.range (k + 1), (-1 : ℝ)^a * (t.choose a : ℝ); let I : ℝ := if t = 0 then 1 else 0; I ≤ U ∧ U - I ≤ (t.choose (k+1) : ℝ) := by
        intro t k hk
        dsimp
        cases t with
        | zero => simp [Finset.sum_range_succ']
        | succ n =>
          have hh := Int.alternating_sum_range_choose_eq_choose (n := n) (m := k)
          have hr : (∑ a ∈ Finset.range (k+1), (-1 : ℝ)^a * ((n+1).choose a : ℝ)) = (-1 : ℝ)^k * (n.choose k : ℝ) := by
            exact_mod_cast hh
          rw [hr, hk.neg_one_pow]
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, one_mul, sub_zero]
          constructor
          · positivity
          · exact_mod_cast (show n.choose k ≤ (n+1).choose (k+1) by rw [Nat.choose_succ_succ]; omega)
      have prodBound : ∀ {ι : Type} [DecidableEq ι] (s : Finset ι) (I U E : ι → ℝ), (∀ i ∈ s, 0 ≤ I i ∧ I i ≤ U i ∧ U i - I i ≤ E i) → (∏ i ∈ s, U i) - (∑ i ∈ s, E i * ∏ j ∈ s.erase i, U j) ≤ (∏ i ∈ s, I i) ∧ (∏ i ∈ s, I i) ≤ (∏ i ∈ s, U i) := by
        intro ι inst s I U E h
        have hU : ∀ i ∈ s, 0 ≤ U i := fun i hi => (h i hi).1.trans (h i hi).2.1
        have hE : ∀ i ∈ s, 0 ≤ E i := fun i hi => (sub_nonneg.mpr (h i hi).2.1).trans (h i hi).2.2
        have upper : (∏ i ∈ s, I i) ≤ ∏ i ∈ s, U i := Finset.prod_le_prod₀ (fun i hi => (h i hi).1) (fun i hi => (h i hi).2.1)
        refine ⟨?_, upper⟩
        suffices gap : (∏ i ∈ s, U i) - (∏ i ∈ s, I i) ≤ ∑ i ∈ s, E i * ∏ j ∈ s.erase i, U j by linarith
        clear upper
        induction s using Finset.induction_on with
        | empty => simp
        | @insert a s ha ih =>
          have hs : ∀ i ∈ s, 0 ≤ I i ∧ I i ≤ U i ∧ U i - I i ≤ E i := fun i hi => h i (Finset.mem_insert_of_mem hi)
          have hsU : ∀ i ∈ s, 0 ≤ U i := fun i hi => hU i (Finset.mem_insert_of_mem hi)
          have hsE : ∀ i ∈ s, 0 ≤ E i := fun i hi => hE i (Finset.mem_insert_of_mem hi)
          have hia := h a (Finset.mem_insert_self a s)
          have hpa : 0 ≤ ∏ i ∈ s, U i := Finset.prod_nonneg hsU
          have hsum : 0 ≤ ∑ i ∈ s, E i * ∏ j ∈ s.erase i, U j := Finset.sum_nonneg (fun i hi => mul_nonneg (hsE i hi) (Finset.prod_nonneg (fun j hj => hsU j (Finset.mem_of_mem_erase hj))))
          have hig := ih hs hsU hsE
          have h1 := mul_le_mul_of_nonneg_right hia.2.2 hpa
          have h2 := mul_le_mul_of_nonneg_left hig hia.1
          have h3 := mul_le_mul_of_nonneg_right hia.2.1 hsum
          have hc : (∑ i ∈ insert a s, E i * ∏ j ∈ (insert a s).erase i, U j) = E a * (∏ j ∈ s, U j) + U a * (∑ i ∈ s, E i * ∏ j ∈ s.erase i, U j) := by
            rw [Finset.sum_insert ha]
            simp only [Finset.erase_insert ha]
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            have hne : i ≠ a := by intro hh; subst i; exact ha hi
            rw [Finset.erase_insert_of_ne hne.symm, Finset.prod_insert]
            · ring
            · exact fun hh => ha (Finset.mem_of_mem_erase hh)
          rw [Finset.prod_insert ha, Finset.prod_insert ha, hc]
          nlinarith
      have boolEval : ∀ {α : Type} [DecidableEq α] (s B : Finset α) (k : ℕ), (∑ d ∈ s.powersetCard k, ∏ p ∈ d, (if p ∈ B then (1 : ℝ) else 0)) = ((s ∩ B).card.choose k : ℝ) := by
        intro α inst s B k
        have hb : ∀ d : Finset α, (∏ p ∈ d, (if p ∈ B then (1 : ℝ) else 0)) = if d ⊆ B then 1 else 0 := by
          intro d
          by_cases hd : d ⊆ B
          · simp [hd, Finset.prod_eq_one (fun p hp => if_pos (hd hp))]
          · rw [if_neg hd]
            have hex : ∃ p ∈ d, p ∉ B := by simpa [Finset.subset_iff] using hd
            obtain ⟨p,hp,hpb⟩ := hex
            exact Finset.prod_eq_zero hp (by simp [hpb])
        simp_rw [hb]
        rw [← Finset.sum_filter]
        have he : (s.powersetCard k).filter (fun d => d ⊆ B) = (s ∩ B).powersetCard k := by
          ext d
          simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_inter_iff]
          tauto
        rw [he]
        simp
      intro ι α instI instA J blocks B k hk
      dsimp only
      let I : ι → ℝ := fun j => if (blocks j ∩ B).card = 0 then 1 else 0
      have hi : (∏ j ∈ J, I j) = if ∀ j ∈ J, blocks j ∩ B = ∅ then 1 else 0 := by
        by_cases h : ∀ j ∈ J, blocks j ∩ B = ∅
        · rw [if_pos h]
          exact Finset.prod_eq_one (fun j hj => by simp [I, h j hj])
        · rw [if_neg h]
          push Not at h
          obtain ⟨j, hj, hb⟩ := h
          exact Finset.prod_eq_zero hj (by simp [I, Finset.card_eq_zero, hb.ne_empty])
      rw [← hi]
      apply prodBound
      intro j hj
      simp_rw [boolEval]
      have hc := countBound (blocks j ∩ B).card (k j) (hk j hj)
      refine ⟨?_, hc⟩
      simp only [I]
      split_ifs <;> norm_num
    intro Ω ι α instI instA objects w bad J blocks k hw hk
    dsimp only
    constructor
    · apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (sandwich J blocks (bad x) k hk).1 (hw x hx)
    · apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (sandwich J blocks (bad x) k hk).2 (hw x hx)
  
  classical
  intro Ω h J blocks z C η objects w bad g r X hz hh hev hC hη hX hw hprime hg hs
  dsimp only
  intro hcount
  let P := Finset.univ.biUnion blocks
  let k := fun j : Fin J => (j.val+1)*h
  let u := fun (v : ℕ → ℝ) j => ∑ n ∈ Finset.range (k j+1), (-1:ℝ)^n * ∑ d ∈ (blocks j).powersetCard n, ∏ p ∈ d, v p
  let e := fun (v : ℕ → ℝ) j => ∑ d ∈ (blocks j).powersetCard (k j+1), ∏ p ∈ d, v p
  let U := fun v => ∏ j, u v j
  let L := fun v => U v - ∑ j, e v j * ∏ i ∈ Finset.univ.erase j, u v i
  let b := fun x p => if p ∈ bad x then (1:ℝ) else 0
  let V := ∏ p ∈ P, (1-g p)
  let ρ := ((Real.exp (Real.exp 1*C)/(1-Real.exp (-1)))/Real.exp (-C/η))*Real.exp (-(h:ℝ))
  let T := (P.powerset.image (fun s => ∏ p ∈ s, p)).filter (fun d : ℕ => (d:ℝ) ≤ z^(4*(h:ℝ)+2))
  let E := ∑ d ∈ ((∏ p ∈ P, p).divisors.filter (fun d : ℕ => Squarefree d ∧ (d:ℝ) ≤ z^(4*(h:ℝ)+2))), |r d|
  let S := ∑ x ∈ objects, w x * (if ∀ j, blocks j ∩ bad x = ∅ then (1:ℝ) else 0)
  have hd := dis J blocks z hz (fun j p hp => (hprime j p hp).2)
  have hp : ∀ j p, p ∈ blocks j → Nat.Prime p ∧ (p:ℝ) ≤ z ^ ((1/2:ℝ)^j.val) := fun j p hp => ⟨(hprime j p hp).1, (hprime j p hp).2.2⟩
  have hR := rem h J blocks z hz hd hp objects w bad g r X hcount
  have hRU := hR false
  have hRL := hR true
  dsimp only at hRU hRL
  simp only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte] at hRU hRL
  have hPU := fun v => (poly blocks k hd v).1
  have hPL := fun v => (poly blocks k hd v).2
  dsimp only at hPU hPL
  have hPUg := hPU g
  have hPLg := hPL g
  have hPUb := fun x => hPU (b x)
  have hPLb := fun x => hPL (b x)
  dsimp only [b,k] at hPUb hPLb
  rw [← hPUg] at hRU
  rw [← hPLg] at hRL
  simp_rw [← hPUb] at hRU
  simp_rw [← hPLb] at hRL
  have hRU' : |(∑ x ∈ objects, w x*U (b x))-X*U g| ≤ ∑ d ∈ T, |r d| := hRU
  have hRL' : |(∑ x ∈ objects, w x*L (b x))-X*L g| ≤ ∑ d ∈ T, |r d| := hRL
  have hP : ∀ p ∈ P, Nat.Prime p := by
    intro p hpp
    obtain ⟨j,hj,hpj⟩ := Finset.mem_biUnion.mp hpp
    exact (hprime j p hpj).1
  have hT : T ⊆ (∏ p ∈ P, p).divisors.filter (fun d : ℕ => Squarefree d ∧ (d:ℝ) ≤ z^(4*(h:ℝ)+2)) := by
    intro d hd
    obtain ⟨hm,hl⟩ := Finset.mem_filter.mp hd
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hm
    have hh := divs P hP s (Finset.mem_powerset.mp hs)
    exact Finset.mem_filter.mpr ⟨hh.1,hh.2,hl⟩
  have hTE : (∑ d ∈ T, |r d|) ≤ E :=
    Finset.sum_le_sum_of_subset_of_nonneg hT (fun d _ _ => abs_nonneg _)
  have hss := sand objects w bad Finset.univ blocks k hw (fun j _ => hev.mul_left (j.val+1))
  have hss' : (∑ x ∈ objects, w x*L (b x)) ≤ S ∧ S ≤ ∑ x ∈ objects, w x*U (b x) := by
    simpa only [Finset.mem_univ, forall_const] using hss
  have hex := expb h J blocks g C η hC hη (by omega) hev hg hs
  have hV : (∏ j, ∏ p ∈ blocks j, (1-g p)) = V :=
    (Finset.prod_biUnion (fun i _ j _ hij => hd i j hij)).symm
  have hex' : 0 ≤ V ∧ 0 ≤ ρ ∧ U g ≤ V*Real.exp ρ ∧ V*(1-ρ*Real.exp ρ) ≤ L g := by
    simpa only [hV] using hex
  have hUp := mul_le_mul_of_nonneg_left hex'.2.2.1 hX
  have hLo := mul_le_mul_of_nonneg_left hex'.2.2.2 hX
  have hru := (abs_le.mp (hRU'.trans hTE)).2
  have hrl := (abs_le.mp (hRL'.trans hTE)).1
  change X*V*(1-ρ*Real.exp ρ)-E ≤ S ∧ S ≤ X*V*Real.exp ρ+E
  constructor <;> nlinarith [hss'.1,hss'.2]

end Green64Analytic.SieveContinuation

end

/-! ## SourceCRTLatticePrefix -/

section

set_option maxHeartbeats 3600000
namespace Green64Analytic.SourceCRT

/-- True count of natural numbers x<N in a prescribed residue class
modulo an arbitrary positive modulus D, not a probabilistic model. -/
def residuePrefixCount (D v N : ℕ) : ℕ :=
   ((Finset.range N).filter (fun x => Nat.ModEq D x v)).card

theorem residuePrefixCount_exact (D v N : ℕ) (hD : 0 < D) :
    residuePrefixCount D v N =
      N/D + if v%D < N%D then 1 else 0 := by
  classical
  unfold residuePrefixCount
  rw [← Nat.count_eq_card_filter_range]
  exact Nat.count_modEq_card N hD v

/-- The dyadic box lattice discrepancy for one residue class,
in its base-prefix form. A genuinely integral bound, not a main
term replaced by its expected density. -/
theorem residuePrefixCount_real_error (D v N : ℕ) (hD : 0 < D) :
    |(residuePrefixCount D v N : ℝ) - (N:ℝ)/(D:ℝ)| ≤ 1 := by
  have hmod : N%D < D := Nat.mod_lt N hD
  have hDr : (0:ℝ) < D := by exact_mod_cast hD
  have hmodr : ((N % D : ℕ) : ℝ) < (D:ℝ) := by exact_mod_cast hmod
  have hsum : (N:ℝ) = ((N / D : ℕ) : ℝ)*(D:ℝ) + ((N % D : ℕ) : ℝ) := by
    have hnat : N = (N/D)*D + N%D := by
      simpa [mul_comm,add_comm] using (Nat.mod_add_div N D).symm
    exact_mod_cast hnat
  have hquot : (N:ℝ)/(D:ℝ) =
      ((N / D : ℕ) : ℝ)+((N % D : ℕ) : ℝ)/(D:ℝ) := by
    field_simp
    nlinarith [hsum]
  have hfrac : 0 ≤ ((N % D : ℕ) : ℝ)/(D:ℝ) ∧
      ((N % D : ℕ) : ℝ)/(D:ℝ) < 1 := by
    constructor
    · positivity
    · exact (div_lt_one hDr).mpr hmodr
  rw [residuePrefixCount_exact D v N hD, hquot]
  by_cases hv : v%D < N%D
  · simp only [ite_eq_left hv]
    push_cast
    rw [abs_le]
    constructor <;> linarith [hfrac.1,hfrac.2]
  · simp only [ite_eq_right hv]
    push_cast
    rw [abs_le]
    constructor <;> linarith [hfrac.1,hfrac.2]

end Green64Analytic.SourceCRT

end

/-! ## SourceCRTLatticeInterval -/

section

set_option maxHeartbeats 4100000
namespace Green64Analytic.SourceCRT

/-- True count in an arbitrary shifted half-open interval [A,B):
this is what dyadic boxes in ex:box require, not only base prefixes. -/
def residueIntervalCount (D v A B : ℕ) : ℕ :=
    ((Finset.Ico A B).filter (fun x => Nat.ModEq D x v)).card

theorem residueIntervalCount_prefix_sub (D v A B : ℕ) (hAB : A ≤ B) :
    residueIntervalCount D v A B =
      residuePrefixCount D v B - residuePrefixCount D v A := by
  classical
  let P : ℕ → Prop := fun x => Nat.ModEq D x v
  have hset : (Finset.range B : Finset ℕ) =
      Finset.range A ∪ Finset.Ico A B := by
    ext x
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj : Disjoint ((Finset.range A).filter P)
      ((Finset.Ico A B).filter P) := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxI
    simp only [Finset.mem_filter, Finset.mem_range,
      Finset.mem_Ico] at hxA hxI
    omega
  have hsum :
      (Finset.range B |>.filter P).card =
        (Finset.range A |>.filter P).card +
        (Finset.Ico A B |>.filter P).card := by
    rw [hset, Finset.filter_union, Finset.card_union_of_disjoint hdisj]
  have hsum' : residuePrefixCount D v B =
      residuePrefixCount D v A + residueIntervalCount D v A B := by
    simpa only [residuePrefixCount,residueIntervalCount,P] using hsum
  omega

theorem residueIntervalCount_real_error (D v A B : ℕ)
    (hD : 0 < D) (hAB : A ≤ B) :
    |(residueIntervalCount D v A B : ℝ) -
      ((B-A:ℕ):ℝ)/(D:ℝ)| ≤ 2 := by
  let CB : ℕ := residuePrefixCount D v B
  let CA : ℕ := residuePrefixCount D v A
  have hCB : CA ≤ CB := by
    have hsub :
        (Finset.range A).filter (fun x => Nat.ModEq D x v) ⊆
        (Finset.range B).filter (fun x => Nat.ModEq D x v) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
      exact ⟨lt_of_lt_of_le hx.1 hAB, hx.2⟩
    exact Finset.card_le_card hsub
  have hCount := residueIntervalCount_prefix_sub D v A B hAB
  have hBoundA := residuePrefixCount_real_error D v A hD
  have hBoundB := residuePrefixCount_real_error D v B hD
  rw [hCount, Nat.cast_sub hCB, Nat.cast_sub hAB]
  change |((CB:ℝ)-(CA:ℝ)) -
       ((B:ℝ)-(A:ℝ))/(D:ℝ)| ≤ 2
  have heq : ((CB:ℝ)-(CA:ℝ)) -
       ((B:ℝ)-(A:ℝ))/(D:ℝ) =
       ((CB:ℝ)-(B:ℝ)/(D:ℝ)) -
       ((CA:ℝ)-(A:ℝ)/(D:ℝ)) := by ring
  rw [heq]
  calc
    _ ≤ |(CB:ℝ)-(B:ℝ)/(D:ℝ)| +
        |(CA:ℝ)-(A:ℝ)/(D:ℝ)| := by
          simpa only [sub_zero, zero_sub, abs_neg] using
            (abs_sub_le ((CB:ℝ)-(B:ℝ)/(D:ℝ)) 0
              ((CA:ℝ)-(A:ℝ)/(D:ℝ)))
    _ ≤ 2 := by
      dsimp [CA,CB] at *
      linarith

end Green64Analytic.SourceCRT

end

