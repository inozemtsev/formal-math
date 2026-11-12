module

public import Green64.Library.Weights.Part081

@[expose] public section

/-!
# Correlation / PhysicalFreeSlotMassBudget

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalFreeSlotMassBudget -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Multiplication is monotone only for nonnegative real factors; this
finite bound avoids assuming the false global `MulLeftMono ℝ` instance. -/
private theorem source_original_B415_nonneg_prod_le_pow434
    {α : Type} [DecidableEq α] (s : Finset α) (f : α → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (h0 : ∀ i ∈ s, 0 ≤ f i)
    (hle : ∀ i ∈ s, f i ≤ c) :
    (∏ i ∈ s, f i) ≤ c ^ s.card := by
  classical
  revert h0 hle
  induction s using Finset.induction_on with
  | empty => intro h0 hle; simp
  | @insert a s ha ih =>
      intro h0 hle
      have hs0 : ∀ i ∈ s, 0 ≤ f i :=
        fun i hi => h0 i (Finset.mem_insert_of_mem hi)
      have hsl : ∀ i ∈ s, f i ≤ c :=
        fun i hi => hle i (Finset.mem_insert_of_mem hi)
      have hprod0 : 0 ≤ ∏ i ∈ s, f i :=
        Finset.prod_nonneg (fun i hi => hs0 i hi)
      have hprod : (∏ i ∈ s, f i) ≤ c ^ s.card := ih hs0 hsl
      calc
        (∏ i ∈ insert a s, f i) = f a * (∏ i ∈ s, f i) := by
          simp only [Finset.prod_insert ha]
        _ ≤ c * (∏ i ∈ s, f i) :=
          mul_le_mul_of_nonneg_right (hle a (Finset.mem_insert_self a s)) hprod0
        _ ≤ c * c ^ s.card := mul_le_mul_of_nonneg_left hprod hc
        _ = c ^ (insert a s).card := by simp [ha, pow_succ, mul_comm]

variable {G : Type} [Fintype G] [DecidableEq G]
variable (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : G) → BP g → ℕ) [∀ g p,NeZero (bm g p)]

/-- TRUE free-slot mass in the original B405--B409 bound for the physically
tilted source law. Shared copies cost 1, free slots cost at most
1 + 2(N+1)/Pmin. No group/OLD/Fock counting is inserted. The remaining
factorial or group-count absorption is a separate downstream obligation. -/
theorem source_original_B415_tilted_free_slot_mass_budget434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ)
    (V : G → ℝ) (hV : ∀ g,V g=∑ p : BP g,1/(bm g p:ℝ))
    (hVpos : ∀ g,0 < V g)
    (Pmin : ℝ) (hPmin : 0 < Pmin)
    (hpmin : ∀ g p,Pmin ≤ (bm g p:ℝ))
    (hsize : ∀ g p,2*((N+1:ℕ):ℝ) ≤ (bm g p:ℝ))
    (J ell m : ℕ) (pat : SourcePattern G J m) :
    (∏ g : G,∏ i : Fin (J+ell),
      if i ∈ sourceBigShared J ell m pat g then (1:ℝ)
      else ∑ p : BP g,physicalSourceMuTilde BP bm q N V g p) ≤
    (1+2*((N+1:ℕ):ℝ)/Pmin)^((J+ell)*(Fintype.card G)) := by
  let c : ℝ := 1+2*((N+1:ℕ):ℝ)/Pmin
  have hcn : 1 ≤ c := by
    dsimp [c]
    have hterm : 0 ≤ 2*((N+1:ℕ):ℝ)/Pmin := by positivity
    linarith only [hterm]
  have hslot (g : G) (i : Fin (J+ell)) :
      (if i ∈ sourceBigShared J ell m pat g then (1:ℝ)
        else ∑ p : BP g,physicalSourceMuTilde BP bm q N V g p) ≤ c := by
    by_cases hs : i ∈ sourceBigShared J ell m pat g
    · simpa only [if_pos hs] using hcn
    · simpa only [if_neg hs,c] using
        (source_original_B414_physical_tilted_group_mass_sharp434
          BP bm q hq hq1 N V hV hVpos Pmin hPmin hpmin hsize g)
  have hc0 : 0 ≤ c := (by norm_num : (0:ℝ) ≤ 1).trans hcn
  have hslot0 (g : G) (i : Fin (J+ell)) :
      0 ≤ (if i ∈ sourceBigShared J ell m pat g then (1:ℝ)
        else ∑ p : BP g,physicalSourceMuTilde BP bm q N V g p) := by
    by_cases hs : i ∈ sourceBigShared J ell m pat g
    · simp [hs]
    · simp only [if_neg hs]
      exact Finset.sum_nonneg (fun p hp =>
        (source_original_B410_physical_mu_tilde_positive_bound434
          BP bm q hq hq1 N V hVpos hsize g p).1.le)
  have hinner (g : G) :
      (∏ i : Fin (J+ell),
        if i ∈ sourceBigShared J ell m pat g then (1:ℝ)
        else ∑ p : BP g,physicalSourceMuTilde BP bm q N V g p) ≤
      c^(J+ell) := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      (source_original_B415_nonneg_prod_le_pow434
        (Finset.univ : Finset (Fin (J+ell)))
        (fun i => if i ∈ sourceBigShared J ell m pat g then (1:ℝ)
          else ∑ p : BP g,physicalSourceMuTilde BP bm q N V g p)
        c hc0 (fun i _ => hslot0 g i) (fun i _ => hslot g i))
  have hinner0 (g : G) :
      0 ≤ ∏ i : Fin (J+ell),
        if i ∈ sourceBigShared J ell m pat g then (1:ℝ)
        else ∑ p : BP g,physicalSourceMuTilde BP bm q N V g p :=
    Finset.prod_nonneg (fun i hi => hslot0 g i)
  have houter :
      (∏ g : G,∏ i : Fin (J+ell),
        if i ∈ sourceBigShared J ell m pat g then (1:ℝ)
        else ∑ p : BP g,physicalSourceMuTilde BP bm q N V g p) ≤
      (c^(J+ell))^(Fintype.card G) := by
    simpa only [Finset.card_univ] using
      (source_original_B415_nonneg_prod_le_pow434
        (Finset.univ : Finset G)
        (fun g => ∏ i : Fin (J+ell),
          if i ∈ sourceBigShared J ell m pat g then (1:ℝ)
          else ∑ p : BP g,physicalSourceMuTilde BP bm q N V g p)
        (c^(J+ell)) (pow_nonneg hc0 _)
        (fun g _ => hinner0 g) (fun g _ => hinner g))
  calc
    _ ≤ (c^(J+ell))^(Fintype.card G) := houter
    _ = c^((J+ell)*(Fintype.card G)) := by rw [pow_mul]
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

end

