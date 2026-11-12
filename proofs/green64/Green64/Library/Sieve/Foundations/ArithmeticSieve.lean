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
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

/-!
# Sieve / Foundations / ArithmeticSieve

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ArithmeticSieve -/

section

namespace Green64Analytic.SieveContinuation
open scoped BigOperators

theorem real_ap_sieve : ∀ (h J : ℕ) (blocks : Fin J → Finset ℕ) (z C A B : ℝ) (q v : ℕ),
1 < z → 2 ≤ h → Even h → 0 ≤ C → 0 ≤ A → A ≤ B → 0 < q →
(∀ j p, p ∈ blocks j → Nat.Prime p ∧ z^((1/2:ℝ)^(j.val+1)) < (p:ℝ) ∧ (p:ℝ) ≤ z^((1/2:ℝ)^j.val)) →
(∀ j p, p ∈ blocks j → q.Coprime p) →
(∀ j, (∑ p ∈ blocks j, (p:ℝ)⁻¹) ≤ C) →
let P := Finset.univ.biUnion blocks;
let V := ∏ p ∈ P, (1-(p:ℝ)⁻¹);
let ρ := ((Real.exp (Real.exp 1*C)/(1-Real.exp (-1)))/Real.exp (-C/(1/2:ℝ)))*Real.exp (-(h:ℝ));
let D := z^(4*(h:ℝ)+2);
let H := (B-A)/q;
let R := (((Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter (fun n => Nat.ModEq q n v ∧ ∀ p ∈ P, ¬ p ∣ n)).card:ℝ);
H*V*(1-ρ*Real.exp ρ)-2*D ≤ R ∧ R ≤ H*V*Real.exp ρ+2*D := by
  have sieve : ∀ {Ω : Type} (h J : ℕ) (blocks : Fin J → Finset ℕ) (z C η : ℝ)
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
              · simp [hd, Finset.prod_eq_one (fun p hp => ite_eq_left (hd hp))]
              · rw [ite_eq_right hd]
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
            · rw [ite_eq_left h]
              apply Finset.prod_eq_one
              intro p hp
              apply ite_eq_right
              intro hpb
              have hm : p ∈ s ∩ B := Finset.mem_inter.mpr ⟨hp,hpb⟩
              rw [Finset.card_eq_zero.mp h] at hm
              exact Finset.notMem_empty p hm
            · rw [ite_eq_right h]
              obtain ⟨p,hp⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
              exact Finset.prod_eq_zero (Finset.mem_inter.mp hp).1 (ite_eq_left (Finset.mem_inter.mp hp).2)
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
                _ = _ := Finset.prod_congr rfl (fun p hp => ite_eq_left hp)
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
            simpa only [Bool.false_eq_true, ite_false, ite_true, mul_zero, mul_one, zero_add] using bern d g (fun _ b => if b then (1:ℝ) else 0)
          have ha : (∑ b, w b * av b) = ∏ p ∈ s, (1-g p) := by
            simpa only [Bool.false_eq_true, ite_false, ite_true, mul_zero, mul_one, add_zero] using bern s g (fun _ b => if b then (0:ℝ) else 1)
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
            exact ite_eq_right (Finset.mem_erase.mp hi).1
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
          · have he : ∀ i, e i = 0 := by intro i; dsimp [e]; exact ite_eq_right (by have := hall i; omega)
            simp only [show ∀ i, (if degree i = k i + 1 then (1:ℝ) else 0) = 0 from he, zero_mul, Finset.sum_const_zero, abs_zero, zero_le_one, sub_zero, true_and]
            exact hp _
          · obtain ⟨j,hj⟩ := not_forall.mp hall
            have hvj : v j = 0 := ite_eq_right hj
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
            _ = _ := by simp [Finset.sum_filter, Finset.mem_range]
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
        · have he : ∀ i, e i = 0 := by intro i; dsimp [e]; exact ite_eq_right (by have := hall i; omega)
          simp only [show ∀ i, (if degree i = k i + 1 then (1:ℝ) else 0) = 0 from he, zero_mul, Finset.sum_const_zero, abs_zero, zero_le_one, sub_zero, true_and]
          exact hp _
        · obtain ⟨j,hj⟩ := not_forall.mp hall
          have hvj : v j = 0 := ite_eq_right hj
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
              have hh : ¬ q ∣ ∏ p ∈ s, p := hq.prime.not_dvd_finsetProd (by
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
              have hh : ¬ q ∣ ∏ p ∈ s, p := hq.prime.not_dvd_finsetProd (by
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
                have hh : ¬ q ∣ ∏ p ∈ s, p := hq.prime.not_dvd_finsetProd (by
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
                have hh : ¬ q ∣ ∏ p ∈ s, p := hq.prime.not_dvd_finsetProd (by
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
      intro objects w bad g r X hcount lower
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
            have hh : ¬ q ∣ ∏ p ∈ s, p := hq.prime.not_dvd_finsetProd (by
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
            · simp [hd, Finset.prod_eq_one (fun p hp => ite_eq_left (hd hp))]
            · rw [ite_eq_right hd]
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
          · rw [ite_eq_left h]
            exact Finset.prod_eq_one (fun j hj => by simp [I, h j hj])
          · rw [ite_eq_right h]
            obtain ⟨j, hj, hb⟩ : ∃ j ∈ J, blocks j ∩ B ≠ ∅ := by
              push Not at h
              simpa only [Finset.nonempty_iff_ne_empty] using h
            exact Finset.prod_eq_zero hj (by simp [I, Finset.card_eq_zero, hb])
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
    simp only [Bool.false_eq_true, ↓reduceIte] at hRU hRL
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
  have joint : ∀ (A B : ℝ) (q v : ℕ) (P s : Finset ℕ),
(∀ p ∈ P, Nat.Prime p) → s ⊆ P →
let I := Finset.Ioc ⌊A⌋₊ ⌊B⌋₊;
let objects := I.filter (fun n => Nat.ModEq q n v);
let bad := fun n => P.filter (fun p => p ∣ n);
let r := fun d : ℕ => ((I.filter (fun n => Nat.ModEq q n v ∧ d ∣ n)).card:ℝ) - (B-A)/(q*d);
(∑ n ∈ objects, (1:ℝ) * ∏ p ∈ s, if p ∈ bad n then (1:ℝ) else 0) =
((B-A)/q)*(∏ p ∈ s, (p:ℝ)⁻¹) + r (∏ p ∈ s, p) := by
    have indicator : ∀ (s : Finset ℕ) (n : ℕ), (∀ p ∈ s, Nat.Prime p) →
  (∏ p ∈ s, (if p ∣ n then (1:ℝ) else 0)) = (if (∏ p ∈ s, p) ∣ n then 1 else 0) := by
      intro s n hp
      have hd : (∏ p ∈ s, p) ∣ n ↔ ∀ p ∈ s, p ∣ n := by
        constructor
        · intro h p hps
          exact dvd_trans (Finset.dvd_prod_of_mem (fun p : ℕ => p) hps) h
        · intro h
          apply Finset.prod_dvd_of_isRelPrime
          · intro p hps q hqs hpq
            exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hp p hps) (hp q hqs)).mpr hpq)
          · exact h
      by_cases h : (∏ p ∈ s, p) ∣ n
      · rw [ite_eq_left h]
        exact Finset.prod_eq_one (fun p hps => ite_eq_left ((hd.mp h) p hps))
      · rw [ite_eq_right h]
        have hh : ∃ p ∈ s, ¬ p ∣ n := by
          by_contra hn
          push Not at hn
          exact h (hd.mpr hn)
        obtain ⟨p,hps,hpn⟩ := hh
        exact Finset.prod_eq_zero hps (ite_eq_right hpn)
    intro A B q v P s hp hs
    dsimp only
    have he (n : ℕ) : (∏ p ∈ s, if p ∈ P.filter (fun p => p ∣ n) then (1:ℝ) else 0) =
        if (∏ p ∈ s, p) ∣ n then 1 else 0 := by
      rw [← indicator s n (fun p hps => hp p (hs hps))]
      apply Finset.prod_congr rfl
      intro p hps
      simp [hs hps]
    simp_rw [one_mul, he]
    have hsum : (∑ n ∈ (Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter (fun n => Nat.ModEq q n v),
        if (∏ p ∈ s, p) ∣ n then (1:ℝ) else 0) =
        (((Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter (fun n => Nat.ModEq q n v ∧ (∏ p ∈ s, p) ∣ n)).card:ℝ) := by
      rw [← Finset.sum_filter]
      simp [Finset.filter_filter]
    rw [hsum]
    have hi : (∏ p ∈ s, (p:ℝ)⁻¹) = ((∏ p ∈ s, p : ℕ):ℝ)⁻¹ := by simp
    rw [hi]
    ring
  have error : ∀ (A B D : ℝ) (q v Q : ℕ), 0 ≤ A → A ≤ B → 0 ≤ D → 0 < q → q.Coprime Q →
let r := fun d : ℕ => (((Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter (fun n => Nat.ModEq q n v ∧ d ∣ n)).card:ℝ) - (B-A)/(q*d);
(∑ d ∈ Q.divisors.filter (fun d : ℕ => Squarefree d ∧ (d:ℝ) ≤ D), |r d|) ≤ 2*D := by
    have count : ∀ (A B : ℝ) (q d v : ℕ), 0 ≤ A → A ≤ B → 0 < q → 0 < d → q.Coprime d →
  |(((Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter (fun n => Nat.ModEq q n v ∧ d ∣ n)).card:ℝ) - (B-A)/(q*d)| ≤ 2 := by
      have count : ∀ (A B : ℝ) (q v : ℕ), 0 ≤ A → A ≤ B → 0 < q →
    |(((Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter (fun n => Nat.ModEq q n v)).card:ℝ) - (B-A)/q| ≤ 2 := by
        have count : ∀ (a b q v : ℕ), a ≤ b → 0 < q →
      |(((Finset.Ioc a b).filter (fun n => Nat.ModEq q n v)).card:ℝ) - ((b:ℝ)-a)/q| ≤ 1 := by
          intro a b q v hab hq
          have hqQ : (0:ℚ) < q := by exact_mod_cast hq
          have hAB : ((a:ℚ)-v)/q ≤ ((b:ℚ)-v)/q :=
            div_le_div_of_nonneg_right (sub_le_sub_right (by exact_mod_cast hab : (a:ℚ) ≤ b) (v:ℚ)) hqQ.le
          have hf : ⌊((a:ℚ)-v)/q⌋ ≤ ⌊((b:ℚ)-v)/q⌋ := Int.floor_mono hAB
          have hc := Nat.Ioc_filter_modEq_card a b hq v
          rw [max_eq_left (sub_nonneg.mpr hf)] at hc
          have hcQ : (((Finset.Ioc a b).filter (fun n => Nat.ModEq q n v)).card:ℚ) =
              (⌊((b:ℚ)-v)/q⌋:ℚ) - (⌊((a:ℚ)-v)/q⌋:ℚ) := by exact_mod_cast hc
          have h1 := Int.floor_le (((a:ℚ)-v)/q)
          have h2 := Int.lt_floor_add_one (((a:ℚ)-v)/q)
          have h3 := Int.floor_le (((b:ℚ)-v)/q)
          have h4 := Int.lt_floor_add_one (((b:ℚ)-v)/q)
          have he : ((b:ℚ)-a)/q = ((b:ℚ)-v)/q-((a:ℚ)-v)/q := by ring
          have hh : |(((Finset.Ioc a b).filter (fun n => Nat.ModEq q n v)).card:ℚ) - ((b:ℚ)-a)/q| ≤ 1 := by
            rw [hcQ,he,abs_le]
            constructor <;> linarith
          have hhR : ((|(((Finset.Ioc a b).filter (fun n => Nat.ModEq q n v)).card:ℚ) - ((b:ℚ)-a)/q| : ℚ):ℝ) ≤ (1:ℝ) := by
            exact_mod_cast hh
          simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast] using hhR
        intro A B q v hA hAB hq
        have hqR : (0:ℝ) < q := by exact_mod_cast hq
        have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
        have h1 := Nat.floor_le hA
        have h2 := Nat.lt_floor_add_one A
        have h3 := Nat.floor_le (hA.trans hAB)
        have h4 := Nat.lt_floor_add_one B
        have he : |((⌊B⌋₊:ℝ)-(⌊A⌋₊:ℝ))-(B-A)| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith
        have hround : |((⌊B⌋₊:ℝ)-(⌊A⌋₊:ℝ))/q-(B-A)/q| ≤ 1 := by
          rw [← sub_div, abs_div, abs_of_pos hqR]
          exact (div_le_one hqR).mpr (he.trans hq1)
        have hc := count ⌊A⌋₊ ⌊B⌋₊ q v (Nat.floor_mono hAB) hq
        calc
          _ = |((((Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter (fun n => Nat.ModEq q n v)).card:ℝ) -
              ((⌊B⌋₊:ℝ)-(⌊A⌋₊:ℝ))/q) + (((⌊B⌋₊:ℝ)-(⌊A⌋₊:ℝ))/q-(B-A)/q)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
          _ ≤ 2 := by linarith
      intro A B q d v hA hAB hq hd hco
    
      let c := Nat.chineseRemainder hco v 0
      have he : (Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter (fun n => Nat.ModEq q n v ∧ d ∣ n) =
          (Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter (fun n => Nat.ModEq (q*d) n c.val) := by
        apply Finset.filter_congr
        intro n hn
        constructor
        · rintro ⟨hnq,hnd⟩
          exact Nat.chineseRemainder_modEq_unique hco hnq (Nat.modEq_zero_iff_dvd.mpr hnd)
        · intro hn
          exact ⟨(hn.of_dvd (dvd_mul_right q d)).trans c.property.1,
            Nat.modEq_zero_iff_dvd.mp ((hn.of_dvd (dvd_mul_left d q)).trans c.property.2)⟩
      rw [he]
      simpa only [Nat.cast_mul] using count A B (q*d) c.val hA hAB (Nat.mul_pos hq hd)
    have level : ∀ (s : Finset ℕ) (D B : ℝ) (r : ℕ → ℝ), 0 ≤ D → 0 ≤ B →
  (∀ d ∈ s, 0 < d ∧ (d:ℝ) ≤ D ∧ |r d| ≤ B) → (∑ d ∈ s, |r d|) ≤ B*D := by
      intro s D B r hD hB hs
      have hsub : s ⊆ Finset.Icc 1 ⌊D⌋₊ := by
        intro d hd
        refine Finset.mem_Icc.mpr ⟨(hs d hd).1,?_⟩
        by_contra hh
        have hn : ⌊D⌋₊+1 ≤ d := by omega
        have hnR : (⌊D⌋₊:ℝ)+1 ≤ d := by exact_mod_cast hn
        have he := Nat.lt_floor_add_one D
        have hb := (hs d hd).2.1
        linarith
      have hc : s.card ≤ ⌊D⌋₊ := by
        simpa using Finset.card_le_card hsub
      have hcR : (s.card:ℝ) ≤ D := (by exact_mod_cast hc : (s.card:ℝ) ≤ ⌊D⌋₊).trans (Nat.floor_le hD)
      calc
        _ ≤ ∑ d ∈ s, B := Finset.sum_le_sum (fun d hd => (hs d hd).2.2)
        _ = B*(s.card:ℝ) := by simp [mul_comm]
        _ ≤ B*D := mul_le_mul_of_nonneg_left hcR hB
    intro A B D q v Q hA hAB hD hq hco
    dsimp only
    apply level _ D 2 _ hD (by norm_num)
    intro d hd
    have hf := Finset.mem_filter.mp hd
    have hdiv := Nat.mem_divisors.mp hf.1
    have hdpos : 0 < d := by
      apply Nat.pos_of_ne_zero
      intro he
      subst d
      exact hdiv.2 (by simpa using hdiv.1)
    exact ⟨hdpos, hf.2.2, count A B q d v hA hAB hq hdpos (Nat.Coprime.of_dvd_right hdiv.1 hco)⟩
  classical
  intro h J blocks z C A B q v hz hh heven hC hA hAB hq hp hcop hsum
  let P := Finset.univ.biUnion blocks
  let I := Finset.Ioc ⌊A⌋₊ ⌊B⌋₊
  let objects := I.filter (fun n => Nat.ModEq q n v)
  let bad := fun n => P.filter (fun p => p ∣ n)
  let r := fun d : ℕ => ((I.filter (fun n => Nat.ModEq q n v ∧ d ∣ n)).card:ℝ) - (B-A)/(q*d)
  have hprime : ∀ p ∈ P, Nat.Prime p := by
    intro p hps
    obtain ⟨j,hj,hpj⟩ := Finset.mem_biUnion.mp hps
    exact (hp j p hpj).1
  have hco : q.Coprime (∏ p ∈ P, p) := by
    apply Nat.coprime_iff_isRelPrime.mpr
    apply IsRelPrime.prod_right
    intro p hps
    obtain ⟨j,hj,hpj⟩ := Finset.mem_biUnion.mp hps
    exact Nat.coprime_iff_isRelPrime.mp (hcop j p hpj)
  have hg : ∀ j p, p ∈ blocks j → 0 ≤ (p:ℝ)⁻¹ ∧ (p:ℝ)⁻¹ ≤ 1-(1/2:ℝ) := by
    intro j p hpj
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (hp j p hpj).1.two_le
    refine ⟨by positivity,?_⟩
    have hi := inv_anti₀ (by norm_num : (0:ℝ) < 2) hp2
    norm_num at hi ⊢
    exact hi
  have hc : ∀ s ⊆ P, (∑ n ∈ objects, (1:ℝ) * ∏ p ∈ s, if p ∈ bad n then (1:ℝ) else 0) =
      ((B-A)/q)*(∏ p ∈ s, (p:ℝ)⁻¹) + r (∏ p ∈ s, p) := by
    intro s hs
    exact joint A B q v P s hprime hs
  have hsieve := sieve h J blocks z C (1/2) objects (fun _ => 1) bad (fun p => (p:ℝ)⁻¹) r ((B-A)/q)
      hz hh heven hC (by norm_num) (div_nonneg (sub_nonneg.mpr hAB) (Nat.cast_nonneg q))
      (by intro n hn; norm_num) hp hg hsum hc
  have herr := error A B (z^(4*(h:ℝ)+2)) q v (∏ p ∈ P, p) hA hAB (Real.rpow_nonneg (by linarith) _) hq hco
  have hav (n : ℕ) : (∀ j, blocks j ∩ bad n = ∅) ↔ ∀ p ∈ P, ¬ p ∣ n := by
    constructor
    · intro ha p hps hpn
      obtain ⟨j,hj,hpj⟩ := Finset.mem_biUnion.mp hps
      have hm : p ∈ blocks j ∩ bad n := Finset.mem_inter.mpr ⟨hpj,Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨j,hj,hpj⟩,hpn⟩⟩
      rw [ha j] at hm
      exact Finset.notMem_empty p hm
    · intro ha j
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hm
      have hb := Finset.mem_inter.mp hm
      have hb' := Finset.mem_filter.mp hb.2
      exact ha p hb'.1 hb'.2
  have hs : (∑ n ∈ objects, (1:ℝ) * (if ∀ j, blocks j ∩ bad n = ∅ then (1:ℝ) else 0)) =
      ((I.filter (fun n => Nat.ModEq q n v ∧ ∀ p ∈ P, ¬ p ∣ n)).card:ℝ) := by
    simp_rw [one_mul,hav]
    rw [← Finset.sum_filter]
    simp [objects, Finset.filter_filter]
  dsimp only at hsieve herr ⊢
  rw [hs] at hsieve
  change _ ≤ 2*z^(4*(h:ℝ)+2) at herr
  constructor
  · linarith [hsieve.1]
  · linarith [hsieve.2]

theorem application_chain : (∀ (h J : ℕ) (blocks : Fin J → Finset ℕ) (z C A B : ℝ) (q v : ℕ),
1 < z → 2 ≤ h → Even h → 0 ≤ C → 0 ≤ A → A ≤ B → 0 < q →
(∀ j p, p ∈ blocks j → Nat.Prime p ∧ z^((1/2:ℝ)^(j.val+1)) < (p:ℝ) ∧ (p:ℝ) ≤ z^((1/2:ℝ)^j.val)) →
(∀ j p, p ∈ blocks j → q.Coprime p) →
(∀ j, (∑ p ∈ blocks j, (p:ℝ)⁻¹) ≤ C) →
let P := Finset.univ.biUnion blocks;
let V := ∏ p ∈ P, (1-(p:ℝ)⁻¹);
let ρ := ((Real.exp (Real.exp 1*C)/(1-Real.exp (-1)))/Real.exp (-C/(1/2:ℝ)))*Real.exp (-(h:ℝ));
let D := z^(4*(h:ℝ)+2);
let H := (B-A)/q;
let R := (((Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter (fun n => Nat.ModEq q n v ∧ ∀ p ∈ P, ¬ p ∣ n)).card:ℝ);
H*V*(1-ρ*Real.exp ρ)-2*D ≤ R ∧ R ≤ H*V*Real.exp ρ+2*D) →
(∀ (h J : ℕ) (blocks : Fin J → Finset ℕ) (z A B : ℝ) (q v : ℕ),
1 < z → 2 ≤ h → Even h → 0 ≤ A → A ≤ B → 0 < q →
(∀ j p, p ∈ blocks j → Nat.Prime p ∧ z^((1/2:ℝ)^(j.val+1)) < (p:ℝ) ∧ (p:ℝ) ≤ z^((1/2:ℝ)^j.val)) →
(∀ j p, p ∈ blocks j → q.Coprime p) →
let P := Finset.univ.biUnion blocks;
let V := ∏ p ∈ P, (1-(p:ℝ)⁻¹);
let K := ((Real.exp (Real.exp 1*4)/(1-Real.exp (-1)))/Real.exp (-4/(1/2:ℝ)));
let D := z^(4*(h:ℝ)+2);
let H := (B-A)/q;
let R := (((Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter (fun n => Nat.ModEq q n v ∧ ∀ p ∈ P, ¬ p ∣ n)).card:ℝ);
|R-H*V| ≤ H*V*(K*Real.exp K)*Real.exp (-(h:ℝ))+2*D) ∧
(∀ (h : ℕ) (P : Finset ℕ) (z A B : ℝ) (q v : ℕ),
1 < z → 2 ≤ h → Even h → 0 ≤ A → A ≤ B → 0 < q →
(∀ p ∈ P, Nat.Prime p ∧ (p:ℝ) ≤ z) →
(∀ p ∈ P, q.Coprime p) →
let V := ∏ p ∈ P, (1-(p:ℝ)⁻¹);
let K := ((Real.exp (Real.exp 1*4)/(1-Real.exp (-1)))/Real.exp (-4/(1/2:ℝ)));
let H := (B-A)/q;
let R := (((Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter (fun n => Nat.ModEq q n v ∧ ∀ p ∈ P, ¬ p ∣ n)).card:ℝ);
|R-H*V| ≤ H*V*(K*Real.exp K)*Real.exp (-(h:ℝ))+2*z^(4*(h:ℝ)+2)) ∧
(∀ (h : ℕ) (z Y δ : ℝ), 1 < z → 2 ≤ h → Even h → 0 ≤ Y → 0 ≤ δ →
let P := (Finset.range (⌊z⌋₊+1)).filter Nat.Prime;
let V := ∏ p ∈ P, (1-(p:ℝ)⁻¹);
let K := ((Real.exp (Real.exp 1*4)/(1-Real.exp (-1)))/Real.exp (-4/(1/2:ℝ)));
let H := (Real.exp δ-1)*Y;
let R := (((Finset.Ioc ⌊Y⌋₊ ⌊Real.exp δ*Y⌋₊).filter (fun n => ∀ p ∈ P, ¬ p ∣ n)).card:ℝ);
|R-H*V| ≤ H*V*(K*Real.exp K)*Real.exp (-(h:ℝ))+2*z^(4*(h:ℝ)+2)) ∧
(∀ (L Y δ : ℝ), 1 < L → 0 ≤ Y → 0 ≤ δ →
let W := Real.exp (Real.sqrt L);
let P := (Finset.range (⌊W⌋₊+1)).filter Nat.Prime;
let V := ∏ p ∈ P, (1-(p:ℝ)⁻¹);
let K := ((Real.exp (Real.exp 1*4)/(1-Real.exp (-1)))/Real.exp (-4/(1/2:ℝ)));
let H := (Real.exp δ-1)*Y;
let R := (((Finset.Ioc ⌊Y⌋₊ ⌊Real.exp δ*Y⌋₊).filter (fun n => ∀ p ∈ P, ¬ p ∣ n)).card:ℝ);
|R-H*V| ≤ H*V*(K*Real.exp K)*Real.exp (-2*(Real.log L)^2) +
  2*Real.exp ((8*(Real.log L)^2+10)*Real.sqrt L)) := by
  intro ap
  have uniform : (∀ (h J : ℕ) (blocks : Fin J → Finset ℕ) (z C A B : ℝ) (q v : ℕ),
1 < z → 2 ≤ h → Even h → 0 ≤ C → 0 ≤ A → A ≤ B → 0 < q →
(∀ j p, p ∈ blocks j → Nat.Prime p ∧ z^((1/2:ℝ)^(j.val+1)) < (p:ℝ) ∧ (p:ℝ) ≤ z^((1/2:ℝ)^j.val)) →
(∀ j p, p ∈ blocks j → q.Coprime p) →
(∀ j, (∑ p ∈ blocks j, (p:ℝ)⁻¹) ≤ C) →
let P := Finset.univ.biUnion blocks;
let V := ∏ p ∈ P, (1-(p:ℝ)⁻¹);
let ρ := ((Real.exp (Real.exp 1*C)/(1-Real.exp (-1)))/Real.exp (-C/(1/2:ℝ)))*Real.exp (-(h:ℝ));
let D := z^(4*(h:ℝ)+2);
let H := (B-A)/q;
let R := (((Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter (fun n => Nat.ModEq q n v ∧ ∀ p ∈ P, ¬ p ∣ n)).card:ℝ);
H*V*(1-ρ*Real.exp ρ)-2*D ≤ R ∧ R ≤ H*V*Real.exp ρ+2*D) →
∀ (h J : ℕ) (blocks : Fin J → Finset ℕ) (z A B : ℝ) (q v : ℕ),
1 < z → 2 ≤ h → Even h → 0 ≤ A → A ≤ B → 0 < q →
(∀ j p, p ∈ blocks j → Nat.Prime p ∧ z^((1/2:ℝ)^(j.val+1)) < (p:ℝ) ∧ (p:ℝ) ≤ z^((1/2:ℝ)^j.val)) →
(∀ j p, p ∈ blocks j → q.Coprime p) →
let P := Finset.univ.biUnion blocks;
let V := ∏ p ∈ P, (1-(p:ℝ)⁻¹);
let K := ((Real.exp (Real.exp 1*4)/(1-Real.exp (-1)))/Real.exp (-4/(1/2:ℝ)));
let D := z^(4*(h:ℝ)+2);
let H := (B-A)/q;
let R := (((Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter (fun n => Nat.ModEq q n v ∧ ∀ p ∈ P, ¬ p ∣ n)).card:ℝ);
|R-H*V| ≤ H*V*(K*Real.exp K)*Real.exp (-(h:ℝ))+2*D := by
    intro ap
    have density : ∀ (z : ℝ) (j : ℕ) (s : Finset ℕ), 1 < z →
  (∀ p ∈ s, Nat.Prime p ∧ z^((1/2:ℝ)^(j+1)) < (p:ℝ) ∧ (p:ℝ) ≤ z^((1/2:ℝ)^j)) →
  (∑ p ∈ s, (p:ℝ)⁻¹) ≤ 4 := by
      have block : ∀ (w : ℝ) (s : Finset ℕ), 1 < w →
    (∀ p ∈ s, Nat.Prime p ∧ w < (p:ℝ) ∧ (p:ℝ) ≤ w^2) →
    (∑ p ∈ s, (p:ℝ)⁻¹) ≤ 4 := by
        have logsum : ∀ (N : ℕ) (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) →
      (∑ p ∈ s, ((N/p:ℕ):ℝ)*Real.log p) ≤ (N:ℝ)*Real.log N := by
          intro N s hp
          have hlocal : ∀ n ∈ Finset.Ioc 0 N, (∑ p ∈ s.filter (fun p => p ∣ n), Real.log (p:ℝ)) ≤ Real.log N := by
            intro n hn
            have hn0 := (Finset.mem_Ioc.mp hn).1
            let t := s.filter (fun p => p ∣ n)
            have ht : ∀ p ∈ t, Nat.Prime p := fun p hpt => hp p (Finset.mem_filter.mp hpt).1
            have hd : (∏ p ∈ t, p) ∣ n := by
              apply Finset.prod_dvd_of_isRelPrime
              · intro p hpt q hqt hpq
                exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (ht p hpt) (ht q hqt)).mpr hpq)
              · intro p hpt
                exact (Finset.mem_filter.mp hpt).2
            have hprodpos : (0:ℝ) < ∏ p ∈ t, (p:ℝ) := Finset.prod_pos (fun p hpt => by exact_mod_cast (ht p hpt).pos)
            have hprodle : (∏ p ∈ t, (p:ℝ)) ≤ N := by
              rw [← Nat.cast_prod]
              exact_mod_cast (Nat.le_of_dvd hn0 hd).trans (Finset.mem_Ioc.mp hn).2
            calc
              _ = Real.log (∏ p ∈ t, (p:ℝ)) := (Real.log_prod (fun p hpt => by exact_mod_cast (ht p hpt).ne_zero)).symm
              _ ≤ Real.log N := Real.log_le_log hprodpos hprodle
          have hswap : (∑ p ∈ s, ((N/p:ℕ):ℝ)*Real.log p) =
              ∑ n ∈ Finset.Ioc 0 N, ∑ p ∈ s.filter (fun p => p ∣ n), Real.log (p:ℝ) := by
            simp only [Finset.sum_filter]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro p hps
            rw [← Finset.sum_filter]
            simp only [Finset.sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]
          rw [hswap]
          calc
            _ ≤ ∑ n ∈ Finset.Ioc 0 N, Real.log (N:ℝ) := Finset.sum_le_sum hlocal
            _ = _ := by simp
        intro w s hw hp
        by_cases hs : s = ∅
        · simp [hs]
        have hw0 : 0 < w := by linarith
        have hlw : 0 < Real.log w := Real.log_pos hw
        let N := ⌊w^2⌋₊
        have hpN : ∀ p ∈ s, p ≤ N := by
          intro p hps
          by_contra hh
          have hn : N+1 ≤ p := by omega
          have hnR : (N:ℝ)+1 ≤ p := by exact_mod_cast hn
          have hh := Nat.lt_floor_add_one (w^2)
          have hpu := (hp p hps).2.2
          change w^2 < (N:ℝ)+1 at hh
          linarith
        obtain ⟨p0,hp0⟩ := Finset.nonempty_iff_ne_empty.mpr hs
        have hN : 0 < N := lt_of_lt_of_le (hp p0 hp0).1.pos (hpN p0 hp0)
        have hNR : (0:ℝ) < N := by exact_mod_cast hN
        have hNlog : Real.log (N:ℝ) ≤ 2*Real.log w := by
          have hnle : (N:ℝ) ≤ w^2 := Nat.floor_le (sq_nonneg w)
          have he := Real.log_le_log hNR hnle
          simpa [Real.log_pow] using he
        have hweight : ∀ p ∈ s, (N:ℝ)*Real.log w*(p:ℝ)⁻¹ ≤ 2*((N/p:ℕ):ℝ)*Real.log p := by
          intro p hps
          have hpp := (hp p hps).1
          have hpR : (0:ℝ) < p := by exact_mod_cast hpp.pos
          have hq : 1 ≤ N/p := Nat.div_pos (hpN p hps) hpp.pos
          have hmod := Nat.mod_lt N hpp.pos
          have hdecomp := Nat.mod_add_div N p
          have hpn : p ≤ p*(N/p) := by simpa using Nat.mul_le_mul_left p hq
          have hNbound : N ≤ 2*(N/p)*p := by nlinarith
          have hNboundR : (N:ℝ) ≤ 2*((N/p:ℕ):ℝ)*(p:ℝ) := by exact_mod_cast hNbound
          have hdiv : (N:ℝ)/(p:ℝ) ≤ 2*((N/p:ℕ):ℝ) := (div_le_iff₀ hpR).mpr hNboundR
          have hlp : Real.log w ≤ Real.log (p:ℝ) := Real.log_le_log hw0 (hp p hps).2.1.le
          calc
            _ = ((N:ℝ)/(p:ℝ))*Real.log w := by ring
            _ ≤ ((N:ℝ)/(p:ℝ))*Real.log (p:ℝ) := mul_le_mul_of_nonneg_left hlp (div_nonneg hNR.le hpR.le)
            _ ≤ _ := mul_le_mul_of_nonneg_right hdiv (hlw.le.trans hlp)
        have hsum := Finset.sum_le_sum hweight
        simp only [← Finset.mul_sum, mul_assoc] at hsum
        have hlog := logsum N s (fun p hps => (hp p hps).1)
        have hfin : (N:ℝ)*Real.log w*(∑ p ∈ s, (p:ℝ)⁻¹) ≤ (N:ℝ)*Real.log w*4 := by
          have hh := mul_le_mul_of_nonneg_left hlog (by norm_num : (0:ℝ) ≤ 2)
          have hh2 := mul_le_mul_of_nonneg_left hNlog (by positivity : (0:ℝ) ≤ 2*(N:ℝ))
          nlinarith
        exact le_of_mul_le_mul_left hfin (mul_pos hNR hlw)
      intro z j s hz hp
      have hw : 1 < z^((1/2:ℝ)^(j+1)) := Real.one_lt_rpow hz (by positivity)
      have he : (z^((1/2:ℝ)^(j+1)))^2 = z^((1/2:ℝ)^j) := by
        calc
          _ = (z^((1/2:ℝ)^(j+1)))^(2:ℝ) := (Real.rpow_natCast _ 2).symm
          _ = z^(((1/2:ℝ)^(j+1))*(2:ℝ)) := (Real.rpow_mul (by linarith : 0 ≤ z) _ _).symm
          _ = _ := by congr 1; rw [pow_succ]; ring
      apply block _ s hw
      intro p hps
      exact ⟨(hp p hps).1, (hp p hps).2.1, he.symm ▸ (hp p hps).2.2⟩
    have algebra : ∀ (X V S E K t : ℝ), 0 ≤ X → 0 ≤ V → 0 ≤ K → 0 ≤ t →
  X*V*(1-(K*Real.exp (-t))*Real.exp (K*Real.exp (-t)))-E ≤ S →
  S ≤ X*V*Real.exp (K*Real.exp (-t))+E →
  |S-X*V| ≤ X*V*(K*Real.exp K)*Real.exp (-t)+E := by
      intro X V S E K t hX hV hK ht hlo hup
      let ρ := K*Real.exp (-t)
      have hr0 : 0 ≤ ρ := mul_nonneg hK (Real.exp_pos _).le
      have hrK : ρ ≤ K := by
        have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        simpa [ρ] using mul_le_mul_of_nonneg_left he hK
      have heρ : Real.exp ρ - 1 ≤ ρ * Real.exp ρ := by
        have he := Real.add_one_le_exp (-ρ)
        have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos ρ).le
        rw [← Real.exp_add] at hm
        simp only [neg_add_cancel,Real.exp_zero] at hm
        nlinarith
      have herr : ρ*Real.exp ρ ≤ (K*Real.exp K)*Real.exp (-t) := by
        have he := Real.exp_le_exp.mpr hrK
        have hh := mul_le_mul_of_nonneg_left he hr0
        dsimp [ρ] at hh ⊢
        nlinarith
      have hXV : 0 ≤ X*V := mul_nonneg hX hV
      have hh := mul_le_mul_of_nonneg_left herr hXV
      have he := mul_le_mul_of_nonneg_left heρ hXV
      change X*V*(1-ρ*Real.exp ρ)-E ≤ S at hlo
      change S ≤ X*V*Real.exp ρ+E at hup
      rw [abs_le]
      constructor <;> nlinarith
    intro h J blocks z A B q v hz hh heven hA hAB hq hp hco
    have hs := ap h J blocks z 4 A B q v hz hh heven (by norm_num) hA hAB hq hp hco
      (fun j => density z j.val (blocks j) hz (hp j))
    have hV : 0 ≤ ∏ p ∈ Finset.univ.biUnion blocks, (1-(p:ℝ)⁻¹) := by
      apply Finset.prod_nonneg
      intro p hps
      obtain ⟨j,hj,hpj⟩ := Finset.mem_biUnion.mp hps
      have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (hp j p hpj).1.two_le
      have hi := inv_anti₀ (by norm_num : (0:ℝ) < 2) hp2
      norm_num at hi
      linarith
    have hd : 0 < 1-Real.exp (-1) := by
      have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
      linarith
    dsimp only at hs ⊢
    apply algebra _ _ _ _ _ (h:ℝ) (div_nonneg (sub_nonneg.mpr hAB) (Nat.cast_nonneg q)) hV
      (by positivity) (Nat.cast_nonneg h) hs.1 hs.2
  have finite : (∀ (h J : ℕ) (blocks : Fin J → Finset ℕ) (z A B : ℝ) (q v : ℕ),
1 < z → 2 ≤ h → Even h → 0 ≤ A → A ≤ B → 0 < q →
(∀ j p, p ∈ blocks j → Nat.Prime p ∧ z^((1/2:ℝ)^(j.val+1)) < (p:ℝ) ∧ (p:ℝ) ≤ z^((1/2:ℝ)^j.val)) →
(∀ j p, p ∈ blocks j → q.Coprime p) →
let P := Finset.univ.biUnion blocks;
let V := ∏ p ∈ P, (1-(p:ℝ)⁻¹);
let K := ((Real.exp (Real.exp 1*4)/(1-Real.exp (-1)))/Real.exp (-4/(1/2:ℝ)));
let D := z^(4*(h:ℝ)+2);
let H := (B-A)/q;
let R := (((Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter (fun n => Nat.ModEq q n v ∧ ∀ p ∈ P, ¬ p ∣ n)).card:ℝ);
|R-H*V| ≤ H*V*(K*Real.exp K)*Real.exp (-(h:ℝ))+2*D) →
∀ (h : ℕ) (P : Finset ℕ) (z A B : ℝ) (q v : ℕ),
1 < z → 2 ≤ h → Even h → 0 ≤ A → A ≤ B → 0 < q →
(∀ p ∈ P, Nat.Prime p ∧ (p:ℝ) ≤ z) →
(∀ p ∈ P, q.Coprime p) →
let V := ∏ p ∈ P, (1-(p:ℝ)⁻¹);
let K := ((Real.exp (Real.exp 1*4)/(1-Real.exp (-1)))/Real.exp (-4/(1/2:ℝ)));
let H := (B-A)/q;
let R := (((Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter (fun n => Nat.ModEq q n v ∧ ∀ p ∈ P, ¬ p ∣ n)).card:ℝ);
|R-H*V| ≤ H*V*(K*Real.exp K)*Real.exp (-(h:ℝ))+2*z^(4*(h:ℝ)+2) := by
    intro ap
    have cutoff : ∀ z : ℝ, 1 < z → ∃ J : ℕ, z^((1/2:ℝ)^J) < 2 := by
      intro z hz
      have hlz : 0 < Real.log z := Real.log_pos hz
      have hl2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
      obtain ⟨J,hJ⟩ := exists_nat_gt (Real.log z / Real.log 2)
      have hpow : ∀ n : ℕ, (n:ℝ)+1 ≤ (2:ℝ)^n := by
        intro n
        induction n with
        | zero => norm_num
        | succ n ih => simp only [pow_succ, Nat.cast_add, Nat.cast_one]; nlinarith
      have hden : 0 < (2:ℝ)^J := by positivity
      have hlarge : Real.log z < (2:ℝ)^J * Real.log 2 := by
        have hh := (div_lt_iff₀ hl2).mp hJ
        have hh2 := mul_le_mul_of_nonneg_right (hpow J) hl2.le
        nlinarith
      have he : Real.log z * (1/2:ℝ)^J < Real.log 2 := by
        rw [div_pow,one_pow, ← mul_div_assoc, mul_one]
        exact (div_lt_iff₀ hden).mpr (by nlinarith)
      refine ⟨J,?_⟩
      rw [Real.rpow_def_of_pos (by linarith : 0 < z)]
      exact (Real.exp_lt_exp.mpr he).trans_eq (Real.exp_log (by norm_num : (0:ℝ) < 2))
    have cover : ∀ (z : ℝ) (P : Finset ℕ) (J : ℕ),
  (∀ p ∈ P, Nat.Prime p ∧ (p:ℝ) ≤ z) → z^((1/2:ℝ)^J) < 2 →
  Finset.univ.biUnion (fun j : Fin J => P.filter (fun p : ℕ => z^((1/2:ℝ)^(j.val+1)) < (p:ℝ) ∧ (p:ℝ) ≤ z^((1/2:ℝ)^j.val))) = P := by
      have cross : ∀ (f : ℕ → ℝ) (p : ℝ) (J : ℕ), p ≤ f 0 → f J < p →
    ∃ j : ℕ, j < J ∧ f (j+1) < p ∧ p ≤ f j := by
        intro f p J
        induction J with
        | zero => intro h1 h2; exact False.elim (not_lt_of_ge h1 h2)
        | succ J ih =>
          intro h1 h2
          by_cases hp : p ≤ f J
          · exact ⟨J,Nat.lt_succ_self J,h2,hp⟩
          · obtain ⟨j,hj,hl,hu⟩ := ih h1 (lt_of_not_ge hp)
            exact ⟨j,Nat.lt_succ_of_lt hj,hl,hu⟩
      intro z P J hp hJ
      ext p
      constructor
      · intro h
        obtain ⟨j,hj,hp⟩ := Finset.mem_biUnion.mp h
        exact (Finset.mem_filter.mp hp).1
      · intro hps
        have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (hp p hps).1.two_le
        have h0 : (p:ℝ) ≤ z^((1/2:ℝ)^0) := by simpa using (hp p hps).2
        obtain ⟨j,hj,hl,hu⟩ := cross (fun j => z^((1/2:ℝ)^j)) (p:ℝ) J h0 (hJ.trans_le hp2)
        exact Finset.mem_biUnion.mpr ⟨⟨j,hj⟩,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hps,hl,hu⟩⟩
    intro h P z A B q v hz hh heven hA hAB hq hp hco
    obtain ⟨J,hJ⟩ := cutoff z hz
    let blocks := fun j : Fin J => P.filter (fun p : ℕ => z^((1/2:ℝ)^(j.val+1)) < (p:ℝ) ∧ (p:ℝ) ≤ z^((1/2:ℝ)^j.val))
    have hgeom : ∀ j p, p ∈ blocks j → Nat.Prime p ∧ z^((1/2:ℝ)^(j.val+1)) < (p:ℝ) ∧ (p:ℝ) ≤ z^((1/2:ℝ)^j.val) := by
      intro j p h
      have hm := Finset.mem_filter.mp h
      exact ⟨(hp p hm.1).1,hm.2⟩
    have hcop : ∀ j p, p ∈ blocks j → q.Coprime p := fun j p h => hco p (Finset.mem_filter.mp h).1
    have hunion : Finset.univ.biUnion blocks = P := cover z P J hp hJ
    have hh := ap h J blocks z A B q v hz hh heven hA hAB hq hgeom hcop
    simpa only [hunion] using hh
  have cell : (∀ (h : ℕ) (P : Finset ℕ) (z A B : ℝ) (q v : ℕ),
1 < z → 2 ≤ h → Even h → 0 ≤ A → A ≤ B → 0 < q →
(∀ p ∈ P, Nat.Prime p ∧ (p:ℝ) ≤ z) →
(∀ p ∈ P, q.Coprime p) →
let V := ∏ p ∈ P, (1-(p:ℝ)⁻¹);
let K := ((Real.exp (Real.exp 1*4)/(1-Real.exp (-1)))/Real.exp (-4/(1/2:ℝ)));
let H := (B-A)/q;
let R := (((Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter (fun n => Nat.ModEq q n v ∧ ∀ p ∈ P, ¬ p ∣ n)).card:ℝ);
|R-H*V| ≤ H*V*(K*Real.exp K)*Real.exp (-(h:ℝ))+2*z^(4*(h:ℝ)+2)) →
∀ (h : ℕ) (z Y δ : ℝ), 1 < z → 2 ≤ h → Even h → 0 ≤ Y → 0 ≤ δ →
let P := (Finset.range (⌊z⌋₊+1)).filter Nat.Prime;
let V := ∏ p ∈ P, (1-(p:ℝ)⁻¹);
let K := ((Real.exp (Real.exp 1*4)/(1-Real.exp (-1)))/Real.exp (-4/(1/2:ℝ)));
let H := (Real.exp δ-1)*Y;
let R := (((Finset.Ioc ⌊Y⌋₊ ⌊Real.exp δ*Y⌋₊).filter (fun n => ∀ p ∈ P, ¬ p ∣ n)).card:ℝ);
|R-H*V| ≤ H*V*(K*Real.exp K)*Real.exp (-(h:ℝ))+2*z^(4*(h:ℝ)+2) := by
    intro sieve
    have mem : ∀ (z : ℝ), 0 ≤ z → ∀ p : ℕ,
  p ∈ (Finset.range (⌊z⌋₊+1)).filter Nat.Prime ↔ Nat.Prime p ∧ (p:ℝ) ≤ z := by
      intro z hz p
      simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
      constructor
      · rintro ⟨hp,hprime⟩
        exact ⟨hprime,(by exact_mod_cast hp : (p:ℝ) ≤ ⌊z⌋₊).trans (Nat.floor_le hz)⟩
      · rintro ⟨hprime,hp⟩
        refine ⟨?_,hprime⟩
        by_contra hh
        have hn : ⌊z⌋₊+1 ≤ p := by omega
        have hnR : (⌊z⌋₊:ℝ)+1 ≤ p := by exact_mod_cast hn
        have he := Nat.lt_floor_add_one z
        linarith
    intro h z Y δ hz hh heven hY hδ
    let P := (Finset.range (⌊z⌋₊+1)).filter Nat.Prime
    have hB : Y ≤ Real.exp δ*Y := by
      have he : 1 ≤ Real.exp δ := Real.one_le_exp_iff.mpr hδ
      nlinarith
    have hs := sieve h P z Y (Real.exp δ*Y) 1 0 hz hh heven hY hB (by norm_num)
      (fun p hp => (mem z (by linarith) p).mp hp)
      (by intro p hp; exact Nat.coprime_one_left p)
    have he : Real.exp δ*Y-Y = (Real.exp δ-1)*Y := by ring
    simpa only [Nat.modEq_one, true_and, Nat.cast_one, div_one, he] using hs
  have growth : (∀ (h : ℕ) (z Y δ : ℝ), 1 < z → 2 ≤ h → Even h → 0 ≤ Y → 0 ≤ δ →
let P := (Finset.range (⌊z⌋₊+1)).filter Nat.Prime;
let V := ∏ p ∈ P, (1-(p:ℝ)⁻¹);
let K := ((Real.exp (Real.exp 1*4)/(1-Real.exp (-1)))/Real.exp (-4/(1/2:ℝ)));
let H := (Real.exp δ-1)*Y;
let R := (((Finset.Ioc ⌊Y⌋₊ ⌊Real.exp δ*Y⌋₊).filter (fun n => ∀ p ∈ P, ¬ p ∣ n)).card:ℝ);
|R-H*V| ≤ H*V*(K*Real.exp K)*Real.exp (-(h:ℝ))+2*z^(4*(h:ℝ)+2)) →
∀ (L Y δ : ℝ), 1 < L → 0 ≤ Y → 0 ≤ δ →
let W := Real.exp (Real.sqrt L);
let P := (Finset.range (⌊W⌋₊+1)).filter Nat.Prime;
let V := ∏ p ∈ P, (1-(p:ℝ)⁻¹);
let K := ((Real.exp (Real.exp 1*4)/(1-Real.exp (-1)))/Real.exp (-4/(1/2:ℝ)));
let H := (Real.exp δ-1)*Y;
let R := (((Finset.Ioc ⌊Y⌋₊ ⌊Real.exp δ*Y⌋₊).filter (fun n => ∀ p ∈ P, ¬ p ∣ n)).card:ℝ);
|R-H*V| ≤ H*V*(K*Real.exp K)*Real.exp (-2*(Real.log L)^2) +
  2*Real.exp ((8*(Real.log L)^2+10)*Real.sqrt L) := by
    intro cell
    have mem : ∀ (z : ℝ), 0 ≤ z → ∀ p : ℕ,
  p ∈ (Finset.range (⌊z⌋₊+1)).filter Nat.Prime ↔ Nat.Prime p ∧ (p:ℝ) ≤ z := by
      intro z hz p
      simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
      constructor
      · rintro ⟨hp,hprime⟩
        exact ⟨hprime,(by exact_mod_cast hp : (p:ℝ) ≤ ⌊z⌋₊).trans (Nat.floor_le hz)⟩
      · rintro ⟨hprime,hp⟩
        refine ⟨?_,hprime⟩
        by_contra hh
        have hn : ⌊z⌋₊+1 ≤ p := by omega
        have hnR : (⌊z⌋₊:ℝ)+1 ≤ p := by exact_mod_cast hn
        have he := Nat.lt_floor_add_one z
        linarith
    intro L Y δ hL hY hδ
    let T := Real.log L
    let h : ℕ := 2*⌈T^2⌉₊
    let W := Real.exp (Real.sqrt L)
    let P := (Finset.range (⌊W⌋₊+1)).filter Nat.Prime
    let V := ∏ p ∈ P, (1-(p:ℝ)⁻¹)
    let K := ((Real.exp (Real.exp 1*4)/(1-Real.exp (-1)))/Real.exp (-4/(1/2:ℝ)))
    let H := (Real.exp δ-1)*Y
    have hT : 0 < T := Real.log_pos hL
    have hceil := Nat.le_ceil (T^2)
    have hceilposR : (0:ℝ) < ⌈T^2⌉₊ := (sq_pos_of_pos hT).trans_le hceil
    have hceilpos : 0 < ⌈T^2⌉₊ := by exact_mod_cast hceilposR
    have hh : 2 ≤ h := by dsimp [h]; omega
    have heven : Even h := ⟨⌈T^2⌉₊,by dsimp [h]; omega⟩
    have hcast : (h:ℝ) = 2*(⌈T^2⌉₊:ℝ) := by simp [h]
    have hsqrt : 0 < Real.sqrt L := Real.sqrt_pos.mpr (by linarith)
    have hW : 1 < W := Real.one_lt_exp_iff.mpr hsqrt
    have hs := cell h W Y δ hW hh heven hY hδ
    have hsmall : Real.exp (-(h:ℝ)) ≤ Real.exp (-2*T^2) := by
      apply Real.exp_le_exp.mpr
      rw [hcast]
      linarith
    have hlarge : W^(4*(h:ℝ)+2) ≤ Real.exp ((8*T^2+10)*Real.sqrt L) := by
      dsimp [W]
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      apply Real.exp_le_exp.mpr
      have hhceil := Nat.ceil_lt_add_one (sq_nonneg T)
      rw [hcast]
      nlinarith
    have hV : 0 ≤ V := by
      apply Finset.prod_nonneg
      intro p hps
      have hp := (mem W (by linarith) p).mp hps
      have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.1.two_le
      have hi := inv_anti₀ (by norm_num : (0:ℝ) < 2) hp2
      norm_num at hi
      linarith
    have hH : 0 ≤ H := mul_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hδ)) hY
    have hden : 0 < 1-Real.exp (-1) := by
      have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
      linarith
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hcoeff : 0 ≤ H*V*(K*Real.exp K) := by positivity
    have hmain := mul_le_mul_of_nonneg_left hsmall hcoeff
    have hrem := mul_le_mul_of_nonneg_left hlarge (by norm_num : (0:ℝ) ≤ 2)
    dsimp only at hs ⊢
    exact hs.trans (add_le_add hmain hrem)
  have hu := uniform ap
  have hf := finite hu
  have hc := cell hf
  exact ⟨hu,hf,hc,growth hc⟩

theorem uniform_ap_sieve : ∀ (h J : ℕ) (blocks : Fin J → Finset ℕ) (z A B : ℝ) (q v : ℕ),
1 < z → 2 ≤ h → Even h → 0 ≤ A → A ≤ B → 0 < q →
(∀ j p, p ∈ blocks j → Nat.Prime p ∧ z^((1/2:ℝ)^(j.val+1)) < (p:ℝ) ∧ (p:ℝ) ≤ z^((1/2:ℝ)^j.val)) →
(∀ j p, p ∈ blocks j → q.Coprime p) →
let P := Finset.univ.biUnion blocks;
let V := ∏ p ∈ P, (1-(p:ℝ)⁻¹);
let K := ((Real.exp (Real.exp 1*4)/(1-Real.exp (-1)))/Real.exp (-4/(1/2:ℝ)));
let D := z^(4*(h:ℝ)+2);
let H := (B-A)/q;
let R := (((Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter (fun n => Nat.ModEq q n v ∧ ∀ p ∈ P, ¬ p ∣ n)).card:ℝ);
|R-H*V| ≤ H*V*(K*Real.exp K)*Real.exp (-(h:ℝ))+2*D := (application_chain real_ap_sieve).1

theorem finite_prime_sieve : ∀ (h : ℕ) (P : Finset ℕ) (z A B : ℝ) (q v : ℕ),
1 < z → 2 ≤ h → Even h → 0 ≤ A → A ≤ B → 0 < q →
(∀ p ∈ P, Nat.Prime p ∧ (p:ℝ) ≤ z) →
(∀ p ∈ P, q.Coprime p) →
let V := ∏ p ∈ P, (1-(p:ℝ)⁻¹);
let K := ((Real.exp (Real.exp 1*4)/(1-Real.exp (-1)))/Real.exp (-4/(1/2:ℝ)));
let H := (B-A)/q;
let R := (((Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter (fun n => Nat.ModEq q n v ∧ ∀ p ∈ P, ¬ p ∣ n)).card:ℝ);
|R-H*V| ≤ H*V*(K*Real.exp K)*Real.exp (-(h:ℝ))+2*z^(4*(h:ℝ)+2) := (application_chain real_ap_sieve).2.1

theorem full_cell_rough_count : ∀ (h : ℕ) (z Y δ : ℝ), 1 < z → 2 ≤ h → Even h → 0 ≤ Y → 0 ≤ δ →
let P := (Finset.range (⌊z⌋₊+1)).filter Nat.Prime;
let V := ∏ p ∈ P, (1-(p:ℝ)⁻¹);
let K := ((Real.exp (Real.exp 1*4)/(1-Real.exp (-1)))/Real.exp (-4/(1/2:ℝ)));
let H := (Real.exp δ-1)*Y;
let R := (((Finset.Ioc ⌊Y⌋₊ ⌊Real.exp δ*Y⌋₊).filter (fun n => ∀ p ∈ P, ¬ p ∣ n)).card:ℝ);
|R-H*V| ≤ H*V*(K*Real.exp K)*Real.exp (-(h:ℝ))+2*z^(4*(h:ℝ)+2) := (application_chain real_ap_sieve).2.2.1

theorem growing_depth_full_cell_rough_count : ∀ (L Y δ : ℝ), 1 < L → 0 ≤ Y → 0 ≤ δ →
let W := Real.exp (Real.sqrt L);
let P := (Finset.range (⌊W⌋₊+1)).filter Nat.Prime;
let V := ∏ p ∈ P, (1-(p:ℝ)⁻¹);
let K := ((Real.exp (Real.exp 1*4)/(1-Real.exp (-1)))/Real.exp (-4/(1/2:ℝ)));
let H := (Real.exp δ-1)*Y;
let R := (((Finset.Ioc ⌊Y⌋₊ ⌊Real.exp δ*Y⌋₊).filter (fun n => ∀ p ∈ P, ¬ p ∣ n)).card:ℝ);
|R-H*V| ≤ H*V*(K*Real.exp K)*Real.exp (-2*(Real.log L)^2) +
  2*Real.exp ((8*(Real.log L)^2+10)*Real.sqrt L) := (application_chain real_ap_sieve).2.2.2

end Green64Analytic.SieveContinuation

end

