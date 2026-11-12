module

public import Green64.Library.Correlation.PhysicalGDilation

@[expose] public section

/-!
# Correlation / PhysicalGAdmissibleHilbert

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalGAdmissibleHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem energy_dilation {H : Type} [Fintype H]
    (pi pi' h : H → ℝ) (hp : ∀ a,0 < pi a) (hp' : ∀ a,0 < pi' a)
    (hh : ∀ a,0 < h a) (hd : ∀ a,pi' a=pi a*(h a)^2) (f : H → ℂ) :
    sourceOriginalSignedJointForwardEnergy434 pi (fun a => (h a:ℂ)*f a) =
      sourceOriginalSignedJointForwardEnergy434 pi' f := by
  rw [source_original_SIGNED_forward_energy_as_sum434 pi (fun a => (hp a).le),
    source_original_SIGNED_forward_energy_as_sum434 pi' (fun a => (hp' a).le)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [hd a,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hh a),mul_pow]
  ring

private theorem energy_similarity {H : Type} [Fintype H]
    (pi pi' h : H → ℝ) (hp : ∀ a,0 < pi a) (hp' : ∀ a,0 < pi' a)
    (hh : ∀ a,0 < h a) (hd : ∀ a,pi' a=pi a*(h a)^2)
    (G G' : H → H → ℂ)
    (hm : ∀ a b,(h a:ℂ)*G' a b=G a b*(h b:ℂ))
    (K : ℝ) (hb : ∀ f,sourceOriginalSignedJointForwardEnergy434 pi'
      (sourceOriginalSignedMatrixAction434 G' f) ≤
      K*sourceOriginalSignedJointForwardEnergy434 pi' f) (f : H → ℂ) :
    sourceOriginalSignedJointForwardEnergy434 pi
      (sourceOriginalSignedMatrixAction434 G f) ≤
      K*sourceOriginalSignedJointForwardEnergy434 pi f := by
  let g : H → ℂ := fun a => f a/(h a:ℂ)
  have hg (a : H) : (h a:ℂ)*g a=f a := by
    have hn : (h a:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hh a).ne'
    dsimp only [g]
    field_simp
  have ha : sourceOriginalSignedMatrixAction434 G f =
      fun a => (h a:ℂ)*sourceOriginalSignedMatrixAction434 G' g a := by
    funext a
    unfold sourceOriginalSignedMatrixAction434
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [←mul_assoc,hm,mul_assoc,hg]
  calc
    _ = sourceOriginalSignedJointForwardEnergy434 pi'
        (sourceOriginalSignedMatrixAction434 G' g) := by
      rw [ha]
      exact energy_dilation pi pi' h hp hp' hh hd _
    _ ≤ K*sourceOriginalSignedJointForwardEnergy434 pi' g := hb g
    _ = K*sourceOriginalSignedJointForwardEnergy434 pi f := by
      rw [←energy_dilation pi pi' h hp hp' hh hd g]
      congr 1
      exact congrArg (sourceOriginalSignedJointForwardEnergy434 pi) (funext hg)

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- The proved diagonal transport gives an operator bound on the original
true density and every joint complex future. No maximum of the dilation
or history-cardinality factor is introduced. -/
theorem source_original_ACTUAL_G_dilation_Hilbert434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho u kappa : ℝ) (N i : ℕ)
    (hR : sourceVisitQ q N i/rho^2=u)
    (hB : sourceVisitEta q N i/rho=(1-u)*kappa)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hk : 0 < kappa)
    (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p)
    (f : H → ℂ) :
    sourceOriginalSignedJointForwardEnergy434
      (sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs V mu)
      (sourceOriginalSignedMatrixAction434
        (sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap q rho N i V mu) f) ≤
    (sourceOriginalFullReturnSchurBudget434 BP (sourceVisitEta u 0 1)
      (fun g => kappa^2*V g) mu)^2 *
      sourceOriginalSignedJointForwardEnergy434
        (sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs V mu) f := by
  let pi := sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs V mu
  let V' := fun g => kappa^2*V g
  let pi' := sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs V' mu
  let h : H → ℝ := fun a => sourceOriginalPendingDilation434 SP sm BP bm (J+ell) kappa a.val.1
  let G := sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap q rho N i V mu
  let G' := sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap u 1 0 1 V' mu
  have hV' (g : BG) : 0 < V' g := mul_pos (sq_pos_of_pos hk) (hV g)
  have hp := source_original_ACTUAL_signed_true_fock_density_pos434
    SP sm BP bm J ell cap Vs V mu hVs hV hmu
  have hp' := source_original_ACTUAL_signed_true_fock_density_pos434
    SP sm BP bm J ell cap Vs V' mu hVs hV' hmu
  have hh (a : H) : 0 < h a := pow_pos hk _
  have hd (a : H) : pi' a=pi a*(h a)^2 :=
    source_original_ACTUAL_density_dilation434 SP sm BP bm J ell cap kappa Vs V mu a
  have hm (a b : H) : (h a:ℂ)*G' a b=G a b*(h b:ℂ) :=
    source_original_ACTUAL_G_dilation434 SP sm BP bm J ell cap hi hcap
      q rho u kappa N i hR hB Vs V mu hVs hmu a b
  apply energy_similarity pi pi' h hp hp' hh hd G G' hm _ _ f
  intro v
  have hs := source_original_SIGNED_forward_exact_Schur434 pi' hp' G' v
  have hc := source_original_ACTUAL_G_true_Schur_gain434 BP bm SP sm J ell cap
    hi hcap u hu hu1 0 1 Vs V' mu hVs hV' hmu
  have hv : 0 ≤ sourceOriginalSignedJointForwardEnergy434 pi' v := by
    rw [source_original_SIGNED_forward_energy_as_sum434 pi' (fun a => (hp' a).le)]
    exact Finset.sum_nonneg (fun a _ => mul_nonneg (hp' a).le (sq_nonneg _))
  calc
    _ ≤ sourceOriginalSignedOneStepSchurGain434 pi' G' *
        sourceOriginalSignedJointForwardEnergy434 pi' v := by
      rw [sourceOriginalSignedOneStepSchurGain434,
        mul_comm (sourceOriginalSignedColumnSchurMax434 pi' G')
          (sourceOriginalSignedRowSchurMax434 G')]
      exact hs
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hv

/-- Explicit finite physical G energy cost at admissible rho. -/
def sourceOriginalAdmissibleGHilbertBudget434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ) : ℝ :=
  ∏ g,∏ p,(1+(sourceVisitEta q N i)^2/(rho^2-sourceVisitQ q N i)*(V g*mu g p))

/-- Unconditional finite operator estimate for the actual G at every
rho with rho^2>sqrt(q), including the compatible fixed rho<1 used by the
proved local DIRTY E saving. The density and joint future are unchanged. -/
theorem source_original_ACTUAL_G_admissible_Hilbert434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hr : 0 < rho) (hgap : Real.sqrt q < rho^2) (N i : ℕ)
    (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p)
    (f : H → ℂ) :
    sourceOriginalSignedJointForwardEnergy434
      (sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs V mu)
      (sourceOriginalSignedMatrixAction434
        (sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap q rho N i V mu) f) ≤
    (sourceOriginalAdmissibleGHilbertBudget434 BP q rho N i V mu)^2 *
      sourceOriginalSignedJointForwardEnergy434
        (sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs V mu) f := by
  let t := sourceVisitQ q N i
  have hs0 := Real.sqrt_nonneg q
  have hs2 := Real.sq_sqrt hq.le
  have hs1 : Real.sqrt q < 1 := by nlinarith
  have hqs : q ≤ Real.sqrt q := by nlinarith
  have ht0 : 0 ≤ t := by
    dsimp only [t,sourceVisitQ]
    split_ifs <;> first | exact hs0 | exact hq.le
  have hts : t ≤ Real.sqrt q := by
    dsimp only [t,sourceVisitQ]
    split_ifs <;> first | exact le_rfl | exact hqs
  have ht1 : t < 1 := hts.trans_lt hs1
  have he : 0 < sourceVisitEta q N i := sub_pos.mpr ht1
  have hd : 0 < rho^2-t := sub_pos.mpr (hts.trans_lt hgap)
  have hr2 : 0 < rho^2 := sq_pos_of_pos hr
  let u := t/rho^2
  let kappa := sourceVisitEta q N i*rho/(rho^2-t)
  have hu : 0 ≤ u := div_nonneg ht0 hr2.le
  have hu1 : u < 1 := (div_lt_one hr2).mpr (hts.trans_lt hgap)
  have hk : 0 < kappa := div_pos (mul_pos he hr) hd
  have hR : sourceVisitQ q N i/rho^2=u := rfl
  have hB : sourceVisitEta q N i/rho=(1-u)*kappa := by
    change (1-t)/rho=(1-t/rho^2)*((1-t)*rho/(rho^2-t))
    field_simp [ne_of_gt hr,ne_of_gt hd]
    <;> ring
  have hf : (1-u)*kappa^2=(sourceVisitEta q N i)^2/(rho^2-t) := by
    change (1-t/rho^2)*((1-t)*rho/(rho^2-t))^2=(1-t)^2/(rho^2-t)
    field_simp [ne_of_gt hr,ne_of_gt hd]
    <;> ring
  have hi0 : sourceVisitEta u 0 1=1-u := by norm_num [sourceVisitEta,sourceVisitQ]
  have hc : sourceOriginalFullReturnSchurBudget434 BP (sourceVisitEta u 0 1)
      (fun g => kappa^2*V g) mu =
      sourceOriginalAdmissibleGHilbertBudget434 BP q rho N i V mu := by
    unfold sourceOriginalFullReturnSchurBudget434 sourceOriginalAdmissibleGHilbertBudget434
    rw [hi0]
    apply Finset.prod_congr rfl
    intro g hg
    apply Finset.prod_congr rfl
    intro p hp
    congr 1
    calc
      (1-u)*(kappa^2*V g*mu g p) = ((1-u)*kappa^2)*(V g*mu g p) := by ring
      _ = _ := by rw [hf]
  have h := source_original_ACTUAL_G_dilation_Hilbert434 SP sm BP bm J ell cap
    hi hcap q rho u kappa N i hR hB hu hu1.le hk Vs V mu hVs hV hmu f
  rw [hc] at h
  exact h

end Green64Analytic.CorrelationSquare

end

end

