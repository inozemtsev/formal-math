module

public import Green64.Library.Weights.Part109
public import Green64.Library.Weights.Part033
public import Green64.Library.Analysis.Estimates.Part015
public import Green64.Library.Weights.Part073
public import Green64.Library.Weights.MarkedProduct
public import Green64.Library.Correlation.Part021
public import Green64.Library.Weights.Part048
public import Green64.Library.Weights.Part096

@[expose] public section

/-!
# Correlation / Part070

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## NormalizedPhysicalDyad -/

section

open Filter Real
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 26000

/-- Actual Parity-normalized physical residual on each dyadic seed.
The harmonic cutoff is literally t*psi(t), with the inherited
normalized log-budget adapter and unchanged Cpsi. The first frequency
is -(rho+xi3), the second is -rho, zeta=-xi3, v0=0; both endpoints
carry the SAME original P-only parity. The factor Z/X retains the
B633 exterior Z and cancels the root normalization X. No extra unit
multiplier or harmonic-cutoff budget is assumed. Full dyadic assembly,
physical restoration and comparison subtraction are separate steps. -/
theorem parity_eventually_actual_normalized_physical_dyad434
    (E Czeta Ck Cpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hE : 0 < E) (hCk : 0 ≤ Ck)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j) :
    ∃ (m : ℕ) (D HH : ℝ) (Cq Cxi J : ℕ) (hmJ : m ≤ J),
      1 ≤ m ∧ 0 ≤ D ∧ 0 ≤ HH ∧
      ∀ (S beta gamma CZ : ℝ), 0 < S → 0 < beta → 0 < gamma → 0 ≤ CZ →
      ∀ᶠ L : ℝ in atTop,
      let Q : ℕ := Nat.ceil (4*L^(D+1))
      let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
      let xi : ℝ := L^(-(Cxi:ℝ))
      1 < L ∧ 0 < Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0 < h ∧ h+h ≤ 1 ∧
      0 < xi ∧ xi⁻¹ ≤ L^Cxi ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (psi : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ psi)
        (hSupport : ∀ x, psi x ≠ 0 → (1/64:ℝ) ≤ x ∧ x ≤ 64),
      sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)) →
      ∀ (xi3 : ℝ), |xi3| ≤ L^Czeta → ∀ (k : ℤ), k ≠ 0 →
        (k.natAbs:ℝ) ≤ L^Ck →
      ∀ (prime : Bool) (l u : ℕ), Real.exp (beta*L) ≤ (l:ℝ) →
      ∀ (r d : ℕ), 1 ≤ r → ∀ (b : Fin (d+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
      let F := sourceNativePrimeCore r d L b slot δ ξ K
        (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
      ∀ xi1 xi2 rho sigma : ℝ,
      let Ecore := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
      let Gcore := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
      ∀ (tw : Bool) (X : ℕ) (Z : ℝ),
        Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ‖((Z/(X:ℝ):ℝ):ℂ) * inner ℂ
          (b655ActualParityFirstVector434 L hFamily J
            (b654ParityIntervalWindow434 J Ck L X (2*X)) X (2*X)
            (b659ActualParityRootCoefficient434 L hFamily J Ecore (-(rho+xi3)) tw X Z 0))
          ((parityActualPsiCutoffMatrix434 L hFamily J m hmJ Q h xi (-xi3) Z (2*k)
            (b654ParityIntervalWindow434 J Ck L X (2*X)) (fun t => (t:ℂ)*psi t)).toEuclideanLin
            (b657ActualPrimeEndpointVector434 L hFamily J
              (b654ParityIntervalWindow434 J Ck L X (2*X)) Gcore (-rho)
                (fun x => (groupSign (sourceOriginalPAllActualBands 20 L)
                  tw x.val.1.val.toNat:ℂ))))‖ ≤ Z*L^(-E) := by
  let K : ℕ → ℝ := sourceNormalizedLogDerivativeConstants 64 Kpsi
  have hK : ∀ j, 0 ≤ K j :=
    source_normalized_log_derivative_constants_nonneg 64 Kpsi (by norm_num) hKpsi
  obtain ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,hActual⟩ :=
    parity_eventually_actual_original_cutoff_all_dyads434
      E Czeta Ck Cpsi K hE hCk hCpsi hK
  refine ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,?_⟩
  intro S beta gamma CZ hS hbeta hgamma hCZ
  filter_upwards [hActual S beta gamma CZ hS hbeta hgamma hCZ] with L hSave
  dsimp only at hSave ⊢
  obtain ⟨hL,hQ,hQc,hh,hh1,hxi,hxic,hFamily0,hSave⟩ := hSave
  refine ⟨hL,hQ,hQc,hh,hh1,hxi,hxic,hFamily0,?_⟩
  intro hFamily psi hSmooth hSupport hReg xi3 hxi3 k hk hkBound prime l u hlow
    r d hr b slot δ ξ Qskip q chi s0 s1
    xi1 xi2 rho sigma tw X Z hZlo hZhi
  have hLp : 0<L := by linarith
  have hZp : 0<Z :=
    (mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  let psiH : ℝ → ℂ := fun t => (t:ℂ)*psi t
  have hSmoothH : ContDiff ℝ ∞ psiH := Complex.ofRealCLM.contDiff.mul hSmooth
  have hSupportH : ∀ t, psiH t ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64 := by
    intro t ht
    apply hSupport t
    intro hz
    exact ht (by simp only [psiH,hz,mul_zero])
  have hRegH : sourceLogDerivativeBudget Cpsi K L (fun u => psiH (Real.exp u)) :=
    source_actual_normalized_log_derivative_budget 64 Cpsi L Kpsi psi
      (by norm_num) hCpsi hKpsi hL.le hSmooth hSupport hReg
  let F := sourceNativePrimeCore r d L b slot δ ξ Qskip
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let Ecore := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let Gcore := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  let positions := b654ParityIntervalWindow434 J Ck L X (2*X)
  let eta : B654ActualParityState434 L hFamily J positions → ℂ :=
    fun x => (groupSign (sourceOriginalPAllActualBands 20 L) tw x.val.1.val.toNat:ℂ)
  have hEta : ∀ x, ‖eta x‖ ≤ 1 := by
    intro x
    change ‖(groupSign (sourceOriginalPAllActualBands 20 L) tw x.val.1.val.toNat:ℂ)‖ ≤ 1
    rw [Complex.norm_real,Real.norm_eq_abs]
    cases tw <;> simp [groupSign,abs_pow]
  have hzeta : |(-xi3)| ≤ L^Czeta := by simpa only [abs_neg] using hxi3
  have hs := hSave hFamily psiH hSmoothH hSupportH hRegH (-xi3) hzeta k hk hkBound
    prime l u hlow r d hr b slot δ ξ Qskip q chi s0 s1
    xi1 xi2 rho sigma (-(rho+xi3)) (-rho) tw X Z 0 hZlo hZhi eta hEta
  let c := b659ActualParityRootCoefficient434 L hFamily J Ecore (-(rho+xi3)) tw X Z 0
  let g := b657ActualPrimeEndpointVector434 L hFamily J positions Gcore (-rho) eta
  let pairing := inner ℂ (b655ActualParityFirstVector434 L hFamily J positions X (2*X) c)
    ((parityActualPsiCutoffMatrix434 L hFamily J m hmJ (Nat.ceil (4*L^(D+1)))
      (Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)) (L^(-(Cxi:ℝ))) (-xi3) Z
      (2*k) positions psiH).toEuclideanLin g)
  change ‖pairing‖ ≤ (X:ℝ)*L^(-E) at hs
  change ‖((Z/(X:ℝ):ℝ):ℂ)*pairing‖ ≤ Z*L^(-E)
  by_cases hX : X=0
  · simp only [hX,Nat.cast_zero,div_zero,Complex.ofReal_zero,zero_mul,norm_zero]
    positivity
  · have hXr : (X:ℝ) ≠ 0 := by exact_mod_cast hX
    have hfac : 0 ≤ Z/(X:ℝ) := div_nonneg hZp.le (Nat.cast_nonneg _)
    calc
      ‖((Z/(X:ℝ):ℝ):ℂ)*pairing‖ = (Z/(X:ℝ))*‖pairing‖ := by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hfac]
      _ ≤ (Z/(X:ℝ))*((X:ℝ)*L^(-E)) := mul_le_mul_of_nonneg_left hs hfac
      _ = Z*L^(-E) := by field_simp; <;> ring
end Green64Analytic.Parity

end

end

/-! ## PhysicalCarrier -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
open Green64Analytic.SourceBlockSieve Green64Analytic.SpectralEndpoint
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 22000
set_option linter.unusedSectionVars false

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell : ℕ)

/-- Inclusion changes only the proof of position membership. Every residue
coordinate and every ordered mark is literally unchanged. -/
def parityPhysicalCarrierInclusion434 {U V : Finset ℤ} (hUV : U ⊆ V)
    (x : B650IntegerPhysicalState434 SP smallMod BP bigMod J ell U) :
    B650IntegerPhysicalState434 SP smallMod BP bigMod J ell V :=
  ⟨(⟨x.val.1.val,hUV x.val.1.property⟩,x.val.2),x.property⟩

theorem parity_physical_carrier_injective434 {U V : Finset ℤ} (hUV : U ⊆ V) :
    Function.Injective (parityPhysicalCarrierInclusion434 SP smallMod BP bigMod J ell hUV) := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun z => z.val.1.val) h
  · exact congrArg (fun z => z.val.2) h

theorem parity_physical_carrier_range434 {U V : Finset ℤ} (hUV : U ⊆ V)
    (y : B650IntegerPhysicalState434 SP smallMod BP bigMod J ell V) :
    (∃ x, parityPhysicalCarrierInclusion434 SP smallMod BP bigMod J ell hUV x = y) ↔
      y.val.1.val ∈ U := by
  constructor
  · rintro ⟨x,rfl⟩
    exact x.val.1.property
  · intro hy
    refine ⟨⟨(⟨y.val.1.val,hy⟩,y.val.2),y.property⟩,?_⟩
    apply Subtype.ext
    rfl

/-- Exact finite reindexing with zero outside an injective image. -/
theorem parity_sum_injective434 {α β M : Type*} [Fintype α] [Fintype β]
    [AddCommMonoid M] (e : α → β) (he : Function.Injective e) (f : β → M)
    (hz : ∀ y, (¬ ∃ x, e x=y) → f y=0) :
    (∑ y : β, f y) = ∑ x : α, f (e x) := by
  classical
  calc
    _ = ∑ y ∈ Finset.univ.image e, f y := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y hy hnot
      apply hz y
      simpa only [Finset.mem_image,Finset.mem_univ,true_and] using hnot
    _ = _ := Finset.sum_image (fun x _ y _ h => he h)

variable (m : ℕ) {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- All original guards, shared/free labels and the signed numerical step
are unchanged by the full-state inclusion. -/
theorem parity_frame_guard_inclusion434 {U V : Finset ℤ} (hUV : U ⊆ V)
    (o k : ℤ) (x y : B650IntegerPhysicalState434 SP smallMod BP bigMod J ell U)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) :
    b650IntegerFrameAllowed434 SP smallMod BP bigMod J ell m patterns V o k
      (parityPhysicalCarrierInclusion434 SP smallMod BP bigMod J ell hUV x)
      (parityPhysicalCarrierInclusion434 SP smallMod BP bigMod J ell hUV y) f ↔
    b650IntegerFrameAllowed434 SP smallMod BP bigMod J ell m patterns U o k x y f := Iff.rfl

/-- The full frame scalar retains auxiliary law, both harmonic masses,
permutations, endpoint damping and the single original Knu exactly. -/
theorem parity_frame_scalar_inclusion434 {U V : Finset ℤ} (hUV : U ⊆ V)
    (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta : ℝ) (o k : ℤ)
    (x y : B650IntegerPhysicalState434 SP smallMod BP bigMod J ell U)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) :
    b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns V q Vs Vb Knu zeta o k
      (parityPhysicalCarrierInclusion434 SP smallMod BP bigMod J ell hUV x)
      (parityPhysicalCarrierInclusion434 SP smallMod BP bigMod J ell hUV y) f =
    b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns U q Vs Vb Knu zeta o k x y f := rfl

/-- The original frame-dependent cutoff is the exact submatrix. -/
theorem parity_psi_matrix_inclusion434 {U V : Finset ℤ} (hUV : U ⊆ V)
    (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta Z : ℝ) (k : ℤ) (psi : ℝ → ℂ)
    (x y : B650IntegerPhysicalState434 SP smallMod BP bigMod J ell U) :
    parityIntegerPsiCutoffMatrix434 SP smallMod BP bigMod J ell m patterns V q Vs Vb Knu zeta Z k psi
      (parityPhysicalCarrierInclusion434 SP smallMod BP bigMod J ell hUV x)
      (parityPhysicalCarrierInclusion434 SP smallMod BP bigMod J ell hUV y) =
    parityIntegerPsiCutoffMatrix434 SP smallMod BP bigMod J ell m patterns U q Vs Vb Knu zeta Z k psi x y := rfl

/-- Seed/frame pairing transport across an injective carrier. The explicit
row-locality premise is later discharged frame by frame for the actual family. -/
theorem parity_seed_frame_transport434
    {α β F : Type*} [Fintype α] [Fintype β] [Fintype F]
    [DecidableEq α] [DecidableEq β]
    (e : α → β) (he : Function.Injective e)
    (posA : α → ℤ) (posB : β → ℤ) (hpos : ∀ x, posB (e x)=posA x)
    (I : Finset ℤ) (w : ℂ) (c : ℤ → ℂ)
    (rowA : α → α → F → ℂ) (rowB : β → β → F → ℂ)
    (gA : EuclideanSpace ℂ α) (gB : EuclideanSpace ℂ β)
    (hrow : ∀ x y t, rowB (e x) (e y) t = rowA x y t)
    (hg : ∀ y, gB (e y)=gA y)
    (hseed : ∀ x, posB x∈I → ∃ y, e y=x)
    (hlocal : ∀ x, posA x∈I → ∀ y, (¬∃ z,e z=y) → ∀ t, rowB (e x) y t=0) :
    inner ℂ (b652FirstPositionVector434 posB w I c)
      ((b658FrameMatrix434 rowB).toEuclideanLin gB) =
    inner ℂ (b652FirstPositionVector434 posA w I c)
      ((b658FrameMatrix434 rowA).toEuclideanLin gA) := by
  rw [b658_seed_frame_pairing434,b658_seed_frame_pairing434]
  calc
    _ = ∑ x : α, ∑ y : β, ∑ t : F,
      if posB (e x)∈I then star (c (posB (e x)))*star w*rowB (e x) y t*gB.ofLp y else 0 := by
      apply parity_sum_injective434 e he
      intro x hx
      have hn : posB x∉I := fun h => hx (hseed x h)
      simp only [hn,ite_false,Finset.sum_const_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hpos]
      by_cases hi : posA x∈I
      · simp only [hi,ite_true]
        calc
          _ = ∑ y : α, ∑ t : F,
            star (c (posA x))*star w*rowB (e x) (e y) t*gB.ofLp (e y) := by
              apply parity_sum_injective434 e he
              intro y hy
              apply Finset.sum_eq_zero
              intro t ht
              rw [hlocal x hi y hy t]
              simp only [mul_zero,zero_mul]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro y hy
            apply Finset.sum_congr rfl
            intro t ht
            rw [hrow]
            change _ * gB (e y) = _ * gA y
            rw [hg]
      · simp only [hi,ite_false,Finset.sum_const_zero]
end Green64FullPhysicalE

end

end

/-! ## DyadicCoefficient -/

section

open scoped BigOperators Classical InnerProductSpace
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE
open Green64Analytic.SpectralEndpoint
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Exact homogeneity of the original source multiplier. Total division
makes this identity valid also at n=0, X=0 and Z=0. -/
theorem parity_source_root_multiplier_scale434 {G : Type} [Fintype G]
    (P : G → Finset ℕ) (tw : Bool) (X Z v : ℝ) (n : ℕ) :
    b656SourceRootMultiplier434 P tw X Z v n =
      (X : ℂ) * b656SourceRootMultiplier434 P tw 1 Z v n := by
  unfold b656SourceRootMultiplier434
  push_cast
  ring

/-- The actual B659 coefficient, retaining parity, both Mellin phases,
the original core and endpoint damping, is exactly X times c_1. -/
theorem parity_actual_root_coefficient_scale434
    (L : ℝ) (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (F : PrimeSlotCore) (t : ℝ) (tw : Bool)
    (X : ℕ) (Z v : ℝ) (n : ℤ) :
    b659ActualParityRootCoefficient434 L hFamily J F t tw X Z v n =
      (X : ℂ) * b659ActualParityRootCoefficient434 L hFamily J F t tw 1 Z v n := by
  unfold b659ActualParityRootCoefficient434
  rw [parity_source_root_multiplier_scale434]
  push_cast
  ring

/-- Scalar linearity of the complete actual first vector. The common
sqrt(mu0) and every ordered mark are unchanged. -/
theorem parity_actual_first_vector_scale434
    (L : ℝ) (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (positions : Finset ℤ) (lo hi : ℕ)
    (c : ℤ → ℂ) (a : ℂ) :
    b655ActualParityFirstVector434 L hFamily J positions lo hi (fun n => a * c n) =
      a • b655ActualParityFirstVector434 L hFamily J positions lo hi c := by
  rw [b655_actual_parity_first_vector_frame434, b655_actual_parity_first_vector_frame434]
  simp only [Finset.smul_sum, smul_smul]

/-- Value identity for the actual first vector at any seed and carrier;
X enters only through the literal numerator of the first coefficient. -/
theorem parity_actual_root_first_vector_scale434
    (L : ℝ) (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (positions : Finset ℤ) (lo hi : ℕ)
    (F : PrimeSlotCore) (t : ℝ) (tw : Bool) (X : ℕ) (Z v : ℝ) :
    b655ActualParityFirstVector434 L hFamily J positions lo hi
      (b659ActualParityRootCoefficient434 L hFamily J F t tw X Z v) =
    (X : ℂ) • b655ActualParityFirstVector434 L hFamily J positions lo hi
      (b659ActualParityRootCoefficient434 L hFamily J F t tw 1 Z v) := by
  have hc : b659ActualParityRootCoefficient434 L hFamily J F t tw X Z v =
      fun n => (X : ℂ) * b659ActualParityRootCoefficient434 L hFamily J F t tw 1 Z v n := by
    funext n
    exact parity_actual_root_coefficient_scale434 L hFamily J F t tw X Z v n
  rw [hc, parity_actual_first_vector_scale434]

/-- Conjugate linearity introduces no extra phase: X is a real natural
scalar. This applies to any complete marked second vector after its
physical cutoff operator has been applied. -/
theorem parity_actual_root_pairing_scale434
    (L : ℝ) (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (positions : Finset ℤ) (lo hi : ℕ)
    (F : PrimeSlotCore) (t : ℝ) (tw : Bool) (X : ℕ) (Z v : ℝ)
    (g : EuclideanSpace ℂ (B654ActualParityState434 L hFamily J positions)) :
    inner ℂ (b655ActualParityFirstVector434 L hFamily J positions lo hi
      (b659ActualParityRootCoefficient434 L hFamily J F t tw X Z v)) g =
    (X : ℂ) * inner ℂ (b655ActualParityFirstVector434 L hFamily J positions lo hi
      (b659ActualParityRootCoefficient434 L hFamily J F t tw 1 Z v)) g := by
  rw [parity_actual_root_first_vector_scale434, inner_smul_left]
  simp

/-- Exact cancellation of the positive dyadic scale in the harmonic
pairing. No norm inequality or analytic estimate is assumed. -/
theorem parity_actual_harmonic_pairing_scale434
    (L : ℝ) (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (positions : Finset ℤ) (lo hi : ℕ)
    (F : PrimeSlotCore) (t : ℝ) (tw : Bool) (X : ℕ) (hX : X ≠ 0) (Z v : ℝ)
    (g : EuclideanSpace ℂ (B654ActualParityState434 L hFamily J positions)) :
    inner ℂ (b655ActualParityFirstVector434 L hFamily J positions lo hi
      (b659ActualParityRootCoefficient434 L hFamily J F t tw 1 Z v)) g =
    ((1 / (X : ℝ) : ℝ) : ℂ) *
      inner ℂ (b655ActualParityFirstVector434 L hFamily J positions lo hi
        (b659ActualParityRootCoefficient434 L hFamily J F t tw X Z v)) g := by
  rw [parity_actual_root_pairing_scale434 L hFamily J positions lo hi F t tw X Z v g]
  have hXC : (X : ℂ) ≠ 0 := by exact_mod_cast hX
  push_cast
  field_simp

/-- The exact disjoint half-open dyadic partition of the literal B654
seed set, expressed as a sum identity for any additive target. -/
theorem parity_dyadic_seed_sum434 {M : Type*} [AddCommMonoid M]
    (T : ℕ) (f : ℤ → M) :
    (∑ n ∈ b654ParitySeedPositions434 1 (2^T), f n) =
      ∑ j ∈ Finset.range T, ∑ n ∈ b654ParitySeedPositions434 (2^j) (2*2^j), f n := by
  simp_rw [b654_sum_seed_positions434]
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, ← ih]
    have hlo : 1 ≤ 2^T := by
      have hp0 : 0 < (2:ℕ)^T := by positivity
      omega
    have hhi : 2^T ≤ 2*2^T := by omega
    have hp : 2^(T+1) = 2*2^T := by ring
    rw [hp]
    exact (Finset.sum_Ico_consecutive (fun n : ℕ => f (n:ℤ)) hlo hhi).symm

/-- Actual full-mark first-vector decomposition on one fixed carrier.
The seed partition is independent of the operator and of all marked
second-endpoint data. No local-carrier transport is hidden here. -/
theorem parity_actual_first_vector_dyadic434
    (L : ℝ) (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (positions : Finset ℤ) (T : ℕ) (c : ℤ → ℂ) :
    b655ActualParityFirstVector434 L hFamily J positions 1 (2^T) c =
      ∑ j ∈ Finset.range T,
        b655ActualParityFirstVector434 L hFamily J positions (2^j) (2*2^j) c := by
  rw [b655_actual_parity_first_vector_frame434, parity_dyadic_seed_sum434]
  apply Finset.sum_congr rfl
  intro j hj
  exact (b655_actual_parity_first_vector_frame434 L hFamily J positions (2^j) (2*2^j) c).symm

/-- Complete harmonic dyadic value identity on a fixed physical carrier.
Local-carrier transport remains a separate exact theorem. -/
theorem parity_actual_harmonic_pairing_dyadic_fixed_carrier434
    (L : ℝ) (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (positions : Finset ℤ) (T : ℕ)
    (F : PrimeSlotCore) (t : ℝ) (tw : Bool) (Z v : ℝ)
    (g : EuclideanSpace ℂ (B654ActualParityState434 L hFamily J positions)) :
    inner ℂ (b655ActualParityFirstVector434 L hFamily J positions 1 (2^T)
      (b659ActualParityRootCoefficient434 L hFamily J F t tw 1 Z v)) g =
      ∑ j ∈ Finset.range T, ((1 / ((2^j:ℕ) : ℝ) : ℝ) : ℂ) *
        inner ℂ (b655ActualParityFirstVector434 L hFamily J positions (2^j) (2*2^j)
          (b659ActualParityRootCoefficient434 L hFamily J F t tw (2^j) Z v)) g := by
  rw [parity_actual_first_vector_dyadic434, sum_inner]
  apply Finset.sum_congr rfl
  intro j hj
  exact parity_actual_harmonic_pairing_scale434 L hFamily J positions (2^j) (2*2^j)
    F t tw (2^j) (by positivity) Z v g

/-- The same exact identity with the ONE original exterior Z. The
coefficients on the right are Z/X_j, not Z squared or an unweighted sum. -/
theorem parity_actual_Z_harmonic_pairing_dyadic_fixed_carrier434
    (L : ℝ) (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (positions : Finset ℤ) (T : ℕ)
    (F : PrimeSlotCore) (t : ℝ) (tw : Bool) (Z v : ℝ)
    (g : EuclideanSpace ℂ (B654ActualParityState434 L hFamily J positions)) :
    (Z : ℂ) * inner ℂ (b655ActualParityFirstVector434 L hFamily J positions 1 (2^T)
      (b659ActualParityRootCoefficient434 L hFamily J F t tw 1 Z v)) g =
      ∑ j ∈ Finset.range T, ((Z / ((2^j:ℕ) : ℝ) : ℝ) : ℂ) *
        inner ℂ (b655ActualParityFirstVector434 L hFamily J positions (2^j) (2*2^j)
          (b659ActualParityRootCoefficient434 L hFamily J F t tw (2^j) Z v)) g := by
  rw [parity_actual_harmonic_pairing_dyadic_fixed_carrier434, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  ring
end Green64Analytic.Parity

end

end

/-! ## HarmonicFrame -/

section

open scoped BigOperators Classical InnerProductSpace
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE
open Green64Analytic.SpectralEndpoint
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 22000

/-- Both square-root lifts contribute exactly the original state mass;
there is no normalization by the cardinality of a mark fibre. -/
theorem parity_sqrt_mass_pair434 (mu : ℝ) (hmu : 0 ≤ mu) :
    star (Real.sqrt mu : ℂ) * (Real.sqrt mu : ℂ) = (mu : ℂ) := by
  have hs : star (Real.sqrt mu : ℂ) = (Real.sqrt mu : ℂ) := by simp
  rw [hs, ← Complex.ofReal_mul, Real.mul_self_sqrt hmu]

/-- Intrinsic nonnegativity of the actual common physical mass. Every
input is a finite sum of reciprocals of natural primes, and total
inversion retains nonnegativity even when a group is empty. -/
theorem parity_actual_state_mass_nonneg434
    (L : ℝ) (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) : 0 ≤ b657ActualStateMass434 L hFamily J := by
  unfold b657ActualStateMass434 b650IntegerStateMass434
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro g hg
    apply div_nonneg zero_le_one
    apply pow_nonneg
    cases g with
    | none =>
      simp only [SourceNativeMemorySmallMass434, sourceNativeOriginalVs434]
      positivity
    | some i =>
      simp only [SourceNativeMemorySmallMass434, sourceNativeOriginalVsmall434]
      positivity
  · apply Finset.prod_nonneg
    intro g hg
    apply div_nonneg zero_le_one
    apply pow_nonneg
    simp only [sourceNativeOriginalVbig434]
    positivity

/-- Finite frame expansion after the two literal sqrt(mu) factors have
been multiplied. The complex signed frame sum remains intact. -/
theorem parity_seed_mass_frame_pairing434
    {α Frame : Type*} [Fintype α] [DecidableEq α] [Fintype Frame]
    (pos : α → ℤ) (mu : ℝ) (hmu : 0 ≤ mu) (I : Finset ℤ)
    (c : ℤ → ℂ) (g : α → ℂ) (row : α → α → Frame → ℂ) :
    inner ℂ (b652FirstPositionVector434 pos (Real.sqrt mu : ℂ) I c)
      ((b658FrameMatrix434 row).toEuclideanLin
        (WithLp.toLp 2 (fun y => (Real.sqrt mu : ℂ) * g y))) =
      ∑ x : α, ∑ y : α, ∑ frame : Frame,
        if pos x ∈ I then (mu : ℂ) * star (c (pos x)) * row x y frame * g y else 0 := by
  rw [b658_seed_frame_pairing434]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro frame hf
  by_cases hI : pos x ∈ I
  · simp only [hI, ite_true, WithLp.ofLp_toLp]
    calc
      star (c (pos x)) * star (Real.sqrt mu : ℂ) * row x y frame *
          ((Real.sqrt mu : ℂ) * g y) =
        (star (Real.sqrt mu : ℂ) * (Real.sqrt mu : ℂ)) *
          star (c (pos x)) * row x y frame * g y := by ring
      _ = _ := by rw [parity_sqrt_mass_pair434 mu hmu]
  · simp only [hI, ite_false]

/-- Independently defined literal finite harmonic physical frame sum.
All actual states and primitive frames, RAW and comparison patterns,
original reciprocal/auxiliary/permutation weights, Knu, shared labels,
full D, and physical displacement 2*k are retained. This definition
contains no dyadic decomposition or matrix pairing. -/
def parityActualHarmonicFrameSum434
    (L : ℝ) (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) : ℂ :=
  let SP := SourceNativeMemorySP434 20 L hFamily
  let BP := SourceNativeMemoryBP434 20 L
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  ∑ x : B654ActualParityState434 L hFamily J positions,
    ∑ y : B654ActualParityState434 L hFamily J positions,
      ∑ frame : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hFamily)
        BP J 1 m pats,
        if x.val.1.val ∈ b654ParitySeedPositions434 lo hi then
          (b657ActualStateMass434 L hFamily J : ℂ) *
          star (b659ActualParityRootCoefficient434 L hFamily J F t1 tw 1 Z v x.val.1.val) *
          b650IntegerFrameScalar434 SP (fun _ p => p.val) BP (fun _ p => p.val)
            J 1 m pats positions (1/2:ℝ) (SourceNativeMemorySmallMass434 20 L hFamily)
            (sourceNativeOriginalVbig434 20 L) Knu zeta 1 (2*k) x y frame *
          psi ((x.val.1.val:ℝ) /
            (Z*(b650NativeFrameD434 SP (fun _ p => p.val) BP (fun _ p => p.val)
              J 1 m pats x.val.2 frame:ℝ))) *
          (groupSign (sourceOriginalPAllActualBands 20 L) tw y.val.1.val.toNat : ℂ) *
          b656IntegerPrimeEndpointCoefficient434 SP (fun _ p => p.val) BP (fun _ p => p.val)
            J 1 (sourceOriginalPAllActualBands 20 L) G (1/2:ℝ) t2 y.val.1.val
        else 0

/-- Exact equality of the actual original-cutoff pairing and the
independent full harmonic frame sum. Actual reciprocal nonnegativity
supplies the sqrt(mu0) identity internally; no norm, support, error,
restoration or correlation estimate is assumed. -/
theorem parity_actual_harmonic_pairing_eq_frames434
    (L : ℝ) (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) :
    inner ℂ (b655ActualParityFirstVector434 L hFamily J positions lo hi
      (b659ActualParityRootCoefficient434 L hFamily J F t1 tw 1 Z v))
      ((parityActualPsiCutoffMatrix434 L hFamily J m hmJ Q h xi zeta Z (2*k)
        positions psi).toEuclideanLin
        (b657ActualPrimeEndpointVector434 L hFamily J positions G t2
          (fun y => (groupSign (sourceOriginalPAllActualBands 20 L)
            tw y.val.1.val.toNat : ℂ)))) =
      parityActualHarmonicFrameSum434 L hFamily J m hmJ Q h xi zeta Z k
        positions lo hi F G t1 t2 tw v psi := by
  let SP := SourceNativeMemorySP434 20 L hFamily
  let BP := SourceNativeMemoryBP434 20 L
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  let eta : B654ActualParityState434 L hFamily J positions → ℂ := fun y =>
    (groupSign (sourceOriginalPAllActualBands 20 L) tw y.val.1.val.toNat : ℂ)
  let d : ℤ → ℂ := b656IntegerPrimeEndpointCoefficient434 SP (fun _ p => p.val)
    BP (fun _ p => p.val) J 1 (sourceOriginalPAllActualBands 20 L) G (1/2:ℝ) t2
  let row := fun (x y : B654ActualParityState434 L hFamily J positions)
      (frame : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hFamily) BP J 1 m pats) =>
    b650IntegerFrameScalar434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 m pats positions (1/2:ℝ) (SourceNativeMemorySmallMass434 20 L hFamily)
      (sourceNativeOriginalVbig434 20 L) Knu zeta 1 (2*k) x y frame *
    psi ((x.val.1.val:ℝ) /
      (Z*(b650NativeFrameD434 SP (fun _ p => p.val) BP (fun _ p => p.val)
        J 1 m pats x.val.2 frame:ℝ)))
  have hf := parity_seed_mass_frame_pairing434
    (fun x : B654ActualParityState434 L hFamily J positions => x.val.1.val)
    (b657ActualStateMass434 L hFamily J) (parity_actual_state_mass_nonneg434 L hFamily J)
    (b654ParitySeedPositions434 lo hi)
    (b659ActualParityRootCoefficient434 L hFamily J F t1 tw 1 Z v)
    (fun y => eta y * d y.val.1.val) row
  simpa only [b655ActualParityFirstVector434, b657ActualPrimeEndpointVector434,
    b657ActualStateMass434, parityActualPsiCutoffMatrix434, parityIntegerPsiCutoffMatrix434,
    parityActualHarmonicFrameSum434, SP, BP, pats, Knu, eta, d, row, mul_assoc] using hf

/-- On positive physical integers the c1 coefficient visibly contains
exactly the original harmonic factor 1/n. The endpoint retains its
arithmetic core, phase and extra damping. -/
theorem parity_actual_root_coefficient_one_positive434
    (L : ℝ) (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (F : PrimeSlotCore) (t : ℝ) (tw : Bool) (Z v : ℝ)
    (n : ℤ) (hn : 0 < n) :
    b659ActualParityRootCoefficient434 L hFamily J F t tw 1 Z v n =
      (groupSign (sourceOriginalPAllActualBands 20 L) tw n.toNat : ℂ) *
      ((1 / (n:ℝ) : ℝ):ℂ) *
      (((n:ℝ) / Z : ℝ):ℂ)^(-Complex.I*(v:ℂ)) *
      b656IntegerPrimeEndpointCoefficient434
        (SourceNativeMemorySP434 20 L hFamily) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1
        (sourceOriginalPAllActualBands 20 L) F (1/2:ℝ) t n := by
  have hnR : (n.toNat:ℝ) = (n:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hn.le
  unfold b659ActualParityRootCoefficient434 b656SourceRootMultiplier434
  simp only [Nat.cast_one, hnR]

/-- The physical harmonic base has root Mellin frequency v=0. -/
theorem parity_actual_root_coefficient_one_zero_phase434
    (L : ℝ) (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (F : PrimeSlotCore) (t : ℝ) (tw : Bool) (Z : ℝ)
    (n : ℤ) (hn : 0 < n) :
    b659ActualParityRootCoefficient434 L hFamily J F t tw 1 Z 0 n =
      (groupSign (sourceOriginalPAllActualBands 20 L) tw n.toNat : ℂ) *
      ((1 / (n:ℝ) : ℝ):ℂ) *
      b656IntegerPrimeEndpointCoefficient434
        (SourceNativeMemorySP434 20 L hFamily) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1
        (sourceOriginalPAllActualBands 20 L) F (1/2:ℝ) t n := by
  rw [parity_actual_root_coefficient_one_positive434 L hFamily J F t tw Z 0 n hn]
  simp
end Green64Analytic.Parity

end

end

/-! ## DyadicSupport -/

section

open Filter Real Green64Analytic.SpectralEndpoint
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.Parity
open Green64Analytic.CorrelationSquare Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 24000

/-- The global harmonic truncation depth depends only on L. -/
def parityDyadicDepth434 (L : ℝ) : ℕ := Nat.ceil (4*L)

/-- The last positive seed endpoint, before selecting any arithmetic data. -/
def parityDyadicLimit434 (L : ℝ) : ℕ := 2 ^ parityDyadicDepth434 L

/-- The exact number of retained dyads is at most 5 L for L at least one. -/
theorem parity_dyadic_depth_bound434 (L : ℝ) (hL : 1 ≤ L) :
    (parityDyadicDepth434 L : ℝ) ≤ 5*L := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hc := (Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ 4*L)).le
  dsimp [parityDyadicDepth434]
  linarith

/-- The global dyadic endpoint is strictly beyond exp(2L), for every L>0.
This is a consequence of the exact ceil and log 2 bound, not a scale premise. -/
theorem parity_dyadic_limit_exp434 (L : ℝ) (hL : 0 < L) :
    Real.exp (2*L) < (parityDyadicLimit434 L : ℝ) := by
  have hlog : (1/2:ℝ) < Real.log 2 := by
    have hh := Real.lt_log_one_add_of_pos (by norm_num : (0:ℝ) < 1)
    norm_num at hh
    linarith
  have hdepth : 4*L ≤ (parityDyadicDepth434 L : ℝ) := Nat.le_ceil _
  have he : 2*L < (parityDyadicDepth434 L : ℝ)*Real.log 2 := by
    calc
      2*L = (4*L)*(1/2:ℝ) := by ring
      _ < (4*L)*Real.log 2 := mul_lt_mul_of_pos_left hlog (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hdepth (by linarith)
  calc
    Real.exp (2*L) < Real.exp ((parityDyadicDepth434 L : ℝ)*Real.log 2) :=
      Real.exp_lt_exp.mpr he
    _ = (2:ℝ) ^ parityDyadicDepth434 L := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    _ = (parityDyadicLimit434 L : ℝ) := by
      simp [parityDyadicLimit434]

/-- The complete actual frame support envelope is below exp(2L).
J and Ck are fixed before L; the later source scale exponent CZ can be any
fixed real. The factor 64 and full physical window are retained. -/
theorem parity_eventually_dyadic_outer_envelope434
    (J : ℕ) (Ck CZ : ℝ) (hCk : 0 ≤ Ck) :
    ∀ᶠ L : ℝ in atTop, Real.exp 1 ≤ L ∧
      64*Real.exp L*L^CZ*(b651ParityWindowSize434 J Ck L : ℝ) < Real.exp (2*L) := by
  filter_upwards [b651_eventually_parity_window_sqrt434 J Ck hCk,
    b638_eventually_poly_exp434 64 CZ (1/2) (by norm_num) (by norm_num),
    b638_eventually_const_power434 4 (1/2) 1 (by norm_num)]
    with L hWindow hPoly hScale
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hWindow.1
  have hPoly' : 64*L^CZ ≤ Real.exp (Real.sqrt L) := by
    simpa only [Real.sqrt_eq_rpow] using hPoly
  have hScale' : 4*Real.sqrt L ≤ L := by
    simpa only [Real.sqrt_eq_rpow, Real.rpow_one] using hScale
  refine ⟨hWindow.1, ?_⟩
  calc
    64*Real.exp L*L^CZ*(b651ParityWindowSize434 J Ck L : ℝ) =
        Real.exp L*((64*L^CZ)*(b651ParityWindowSize434 J Ck L : ℝ)) := by ring
    _ ≤ Real.exp L*(Real.exp (Real.sqrt L)*Real.exp (Real.sqrt L)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hPoly' hWindow.2 (Nat.cast_nonneg _) (Real.exp_nonneg _))
        (Real.exp_nonneg _)
    _ = Real.exp (L+2*Real.sqrt L) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ < Real.exp (2*L) := Real.exp_lt_exp.mpr (by linarith)

/-- Every nonzero cutoff on every complete actual physical frame has its
source integer in the fixed seed [1,2^ceil(4L)). This retains all repeated
shared factors and all auxiliary draws in the literal D_frame. The assertion
is uniform in the pattern family, frame, source state, cutoff and carrier. -/
theorem parity_eventually_actual_frame_dyadic_support434
    (J : ℕ) (Ck CZ : ℝ) (hCk : 0 ≤ Ck) :
    ∀ᶠ L : ℝ in atTop, Real.exp 1 ≤ L ∧
    ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (m : ℕ) {Nu : Type} [Fintype Nu]
      (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
      (x : MemoryIndependentState
        (SourceNativeMemorySP434 20 L hFamily) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1)
      (f : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hFamily)
        (SourceNativeMemoryBP434 20 L) J 1 m patterns)
      (Z : ℝ), 0 < Z → Z ≤ Real.exp L*L^CZ →
    ∀ (psi : ℝ → ℂ),
      (∀ u, psi u ≠ 0 → (1/64:ℝ) ≤ u ∧ u ≤ 64) →
    ∀ (n : ℤ),
      psi ((n:ℝ)/(Z*(b650NativeFrameD434
        (SourceNativeMemorySP434 20 L hFamily) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
        J 1 m patterns x f:ℝ))) ≠ 0 →
      0 < n ∧ n < (parityDyadicLimit434 L : ℤ) := by
  filter_upwards [parity_eventually_dyadic_outer_envelope434 J Ck CZ hCk]
    with L hEnv
  refine ⟨hEnv.1, ?_⟩
  intro hFamily m Nu instNu patterns x f Z hZp hZhi psi hSupport n hpsi
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hEnv.1
  let D := b650NativeFrameD434
    (SourceNativeMemorySP434 20 L hFamily) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
    J 1 m patterns x f
  have hD : 0 < D := b658_native_frame_divisor_pos434
    (SourceNativeMemorySP434 20 L hFamily) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
    J 1 m patterns x f
  have hDr : (0:ℝ) < D := by exact_mod_cast hD
  have hZD : 0 < Z*(D:ℝ) := mul_pos hZp hDr
  have hDH : (D:ℝ) ≤ (b651ParityWindowSize434 J Ck L:ℝ) :=
    b660_actual_parity_frame_D_window434 L hEnv.1 hFamily J m Ck hCk patterns x f
  have hs := hSupport _ hpsi
  have hnlo : (1/64:ℝ)*(Z*(D:ℝ)) ≤ (n:ℝ) := (le_div_iff₀ hZD).mp hs.1
  have hnhi : (n:ℝ) ≤ 64*(Z*(D:ℝ)) := (div_le_iff₀ hZD).mp hs.2
  have hnpos : (0:ℝ) < n :=
    (mul_pos (by norm_num : (0:ℝ)<1/64) hZD).trans_le hnlo
  have hnend : (n:ℝ) < (parityDyadicLimit434 L:ℝ) := by
    calc
      (n:ℝ) ≤ 64*(Z*(D:ℝ)) := hnhi
      _ ≤ 64*((Real.exp L*L^CZ)*(b651ParityWindowSize434 J Ck L:ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hZhi hDH hDr.le
            (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hLp.le _))) (by norm_num)
      _ = 64*Real.exp L*L^CZ*(b651ParityWindowSize434 J Ck L:ℝ) := by ring
      _ < Real.exp (2*L) := hEnv.2
      _ < (parityDyadicLimit434 L:ℝ) := parity_dyadic_limit_exp434 L hLp
  constructor
  · exact_mod_cast hnpos
  · exact_mod_cast hnend

/-- Exact disappearance of both nonpositive seeds and the outer harmonic
tail, frame by frame. It does not infer cutoff locality from cancellation of
an uncut matrix. -/
theorem parity_eventually_actual_frame_dyadic_tail_zero434
    (J : ℕ) (Ck CZ : ℝ) (hCk : 0 ≤ Ck) :
    ∀ᶠ L : ℝ in atTop, Real.exp 1 ≤ L ∧
    ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (m : ℕ) {Nu : Type} [Fintype Nu]
      (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
      (x : MemoryIndependentState
        (SourceNativeMemorySP434 20 L hFamily) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1)
      (f : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hFamily)
        (SourceNativeMemoryBP434 20 L) J 1 m patterns)
      (Z : ℝ), 0 < Z → Z ≤ Real.exp L*L^CZ →
    ∀ (psi : ℝ → ℂ),
      (∀ u, psi u ≠ 0 → (1/64:ℝ) ≤ u ∧ u ≤ 64) →
    ∀ (n : ℤ), n ≤ 0 ∨ (parityDyadicLimit434 L : ℤ) ≤ n →
      psi ((n:ℝ)/(Z*(b650NativeFrameD434
        (SourceNativeMemorySP434 20 L hFamily) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
        J 1 m patterns x f:ℝ))) = 0 := by
  filter_upwards [parity_eventually_actual_frame_dyadic_support434 J Ck CZ hCk]
    with L hSupportAll
  refine ⟨hSupportAll.1, ?_⟩
  intro hFamily m Nu instNu patterns x f Z hZp hZhi psi hSupport n hout
  by_contra hne
  have hs := hSupportAll.2 hFamily m patterns x f Z hZp hZhi psi hSupport n hne
  rcases hout with hnonpos | houter
  · exact (not_lt_of_ge hnonpos) hs.1
  · exact (not_lt_of_ge houter) hs.2

/-- Two spare logarithmic powers absorb the exact dyad count, with unit
constant and exactly one exterior Z. The terms are already normalized dyads. -/
theorem parity_dyadic_sum_loss434 (A L Z : ℝ) (hL : 5 ≤ L) (hZ : 0 ≤ Z)
    (v : ℕ → ℂ)
    (hv : ∀ j < parityDyadicDepth434 L, ‖v j‖ ≤ Z*L^(-(A+2))) :
    ‖∑ j ∈ Finset.range (parityDyadicDepth434 L), v j‖ ≤ Z*L^(-A) := by
  have hLp : 0 < L := by linarith
  have hT := parity_dyadic_depth_bound434 L (by linarith)
  have hT2 : (parityDyadicDepth434 L:ℝ) ≤ L^2 := by
    have hh : 0 ≤ L*(L-5) := mul_nonneg hLp.le (by linarith)
    nlinarith
  calc
    ‖∑ j ∈ Finset.range (parityDyadicDepth434 L), v j‖ ≤
        ∑ j ∈ Finset.range (parityDyadicDepth434 L), ‖v j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (parityDyadicDepth434 L), Z*L^(-(A+2)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hv j (Finset.mem_range.mp hj)
    _ = (parityDyadicDepth434 L:ℝ)*(Z*L^(-(A+2))) := by simp
    _ ≤ L^2*(Z*L^(-(A+2))) :=
      mul_le_mul_of_nonneg_right hT2 (mul_nonneg hZ (Real.rpow_nonneg hLp.le _))
    _ = Z*(L^(2:ℝ)*L^(-(A+2))) := by rw [Real.rpow_two]; ring
    _ = Z*L^(2+(-(A+2))) := by rw [← Real.rpow_add hLp]
    _ = Z*L^(-A) := by congr 2; ring

/-- The same full physical matrix pairing is unchanged when any larger
positive seed interval is truncated at N(L). This is a literal identity on
an arbitrary fixed finite carrier. No decay error, mark-fibre normalization,
transport assumption or equality of already summed uncut matrices is used. -/
theorem parity_eventually_actual_cutoff_seed_truncation434
    (J : ℕ) (Ck CZ : ℝ) (hCk : 0 ≤ Ck) :
    ∀ᶠ L : ℝ in atTop, Real.exp 1 ≤ L ∧
    ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ)
      (k : ℤ) (positions : Finset ℤ) (M : ℕ),
      parityDyadicLimit434 L ≤ M → 0 < Z → Z ≤ Real.exp L*L^CZ →
    ∀ (psi : ℝ → ℂ),
      (∀ u, psi u ≠ 0 → (1/64:ℝ) ≤ u ∧ u ≤ 64) →
    ∀ (c : ℤ → ℂ)
      (g : EuclideanSpace ℂ (B654ActualParityState434 L hFamily J positions)),
      inner ℂ (b655ActualParityFirstVector434 L hFamily J positions 1 M c)
        ((parityActualPsiCutoffMatrix434 L hFamily J m hmJ Q h xi zeta Z (2*k)
          positions psi).toEuclideanLin g) =
      inner ℂ
        (b655ActualParityFirstVector434 L hFamily J positions 1 (parityDyadicLimit434 L) c)
        ((parityActualPsiCutoffMatrix434 L hFamily J m hmJ Q h xi zeta Z (2*k)
          positions psi).toEuclideanLin g) := by
  filter_upwards [parity_eventually_actual_frame_dyadic_tail_zero434 J Ck CZ hCk]
    with L hTail
  refine ⟨hTail.1, ?_⟩
  intro hFamily m hmJ Q h xi zeta Z k positions M hNM hZp hZhi psi hSupport c g
  have hSub : b654ParitySeedPositions434 1 (parityDyadicLimit434 L) ⊆
      b654ParitySeedPositions434 1 M := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_image.mpr ⟨a,
      Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp ha).1,
        (Finset.mem_Ico.mp ha).2.trans_le hNM⟩, rfl⟩
  unfold parityActualPsiCutoffMatrix434 parityIntegerPsiCutoffMatrix434
  change inner ℂ (b652FirstPositionVector434 _ _ _ _)
    ((b658FrameMatrix434 _).toEuclideanLin g) =
    inner ℂ (b652FirstPositionVector434 _ _ _ _)
      ((b658FrameMatrix434 _).toEuclideanLin g)
  rw [b658_seed_frame_pairing434, b658_seed_frame_pairing434]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro f hf
  by_cases hnN : x.val.1.val ∈ b654ParitySeedPositions434 1 (parityDyadicLimit434 L)
  · have hnM := hSub hnN
    simp only [hnN, hnM, ite_true]
  · by_cases hnM : x.val.1.val ∈ b654ParitySeedPositions434 1 M
    · have hnCap : (parityDyadicLimit434 L : ℤ) ≤ x.val.1.val := by
        obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hnM
        have haN : parityDyadicLimit434 L ≤ a := by
          by_contra hnot
          exact hnN (Finset.mem_image.mpr ⟨a,
            Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp ha).1, lt_of_not_ge hnot⟩, he⟩)
        calc
          (parityDyadicLimit434 L : ℤ) ≤ (a:ℤ) := by exact_mod_cast haN
          _ = x.val.1.val := he
      have hCut := hTail.2 hFamily m
        (sourceOriginalMemoryRawComparisonPattern434
          (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
          J m hmJ) x.val.2 f Z hZp hZhi psi hSupport x.val.1.val (Or.inr hnCap)
      simp only [hnN, hnM, ite_false, ite_true, hCut, mul_zero, zero_mul]
    · simp only [hnN, hnM, ite_false]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## FrameLocality -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 20000

/-- The full original numerical displacement of EVERY actual Parity frame
is bounded by the interval margin R, before summing any signed frames.
All ordered marks, shared factors, patterns and repeated auxiliary draws
remain in the literal native D. No nonvanishing summed-matrix premise is
used, and the conclusion is the radius rather than the larger 2R+1. -/
theorem parity_actual_frame_radius434
    (J m : ℕ) (Ck L : ℝ) (hL : Real.exp 1 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
    (x : MemoryIndependentState
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1)
    (frame : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J 1 m patterns)
    (k : ℤ) (hk : (k.natAbs:ℝ) ≤ L^Ck) :
    |2*k*(b650NativeFrameD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x frame:ℤ)| ≤ (b651ParityPathRadius434 J Ck L:ℤ) := by
  let ω := b643AllPrimePathOf434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
    J 1 m patterns (fun _ : Fin 2 => x) (fun _ : Fin 1 => frame)
  have hD := b651_actual_parity_shift_D_cap434 J m Ck L hL hS patterns ω 0 k hk
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hR := (b651_parity_maxstep_window_bounds434 J Ck L hL1).1
  have hb : |((2*k*(b650NativeFrameD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x frame:ℤ):ℤ):ℝ)| ≤ (b651ParityPathRadius434 J Ck L:ℝ) :=
    hD.trans hR
  exact_mod_cast hb

/-- A source seed and the original frame guard force its target into
the exact local interval carrier, even when both endpoints are initially
represented on a different common finite carrier. -/
theorem parity_actual_allowed_frame_target_in_window434
    (J m : ℕ) (Ck L : ℝ) (hL : Real.exp 1 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
    (k : ℤ) (hk : (k.natAbs:ℝ) ≤ L^Ck)
    (positions : Finset ℤ) (lo hi : ℕ)
    (x y : B654ActualParityState434 L hS J positions)
    (frame : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J 1 m patterns)
    (hx : x.val.1.val ∈ b654ParitySeedPositions434 lo hi)
    (ha : b650IntegerFrameAllowed434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns positions 1 (2*k) x y frame) :
    y.val.1.val ∈ b654ParityIntervalWindow434 J Ck L lo hi := by
  have hR := parity_actual_frame_radius434 J m Ck L hL hS patterns x.val.2 frame k hk
  have hoff : y.val.1.val-x.val.1.val =
      2*k*(b650NativeFrameD434
        (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
        J 1 m patterns x.val.2 frame:ℤ) := by
    rw [ha.2.2.2.2]
    ring
  have hdist : |y.val.1.val-x.val.1.val| ≤ (b651ParityPathRadius434 J Ck L:ℤ) := by
    rw [hoff]
    exact hR
  obtain ⟨n,hn,heq⟩ := Finset.mem_image.mp hx
  obtain ⟨hnlo,hnhi⟩ := Finset.mem_Ico.mp hn
  have hlo : (lo:ℤ) ≤ x.val.1.val := by omega
  have hhi : x.val.1.val < (hi:ℤ) := by omega
  obtain ⟨hdlo,hdhi⟩ := abs_le.mp hdist
  apply Finset.mem_Icc.mpr
  constructor <;> omega

/-- Outside the local carrier each original frame scalar is exactly
zero. This precedes multiplication by a frame-dependent cutoff, so
cancellation between distinct frames is never used for support. -/
theorem parity_actual_frame_scalar_zero_outside434
    (J m : ℕ) (Ck L : ℝ) (hL : Real.exp 1 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
    (k : ℤ) (hk : (k.natAbs:ℝ) ≤ L^Ck)
    (positions : Finset ℤ) (lo hi : ℕ)
    (q : ℝ) (Vs : SourceNativeMemorySG434 20 L hS → ℝ)
    (Vb : sourceNativeOriginalBigType434 20 L → ℝ)
    (Knu : SourcePatternK (SourceNativeMemoryBP434 20 L) J 1 m patterns)
    (zeta : ℝ) (x y : B654ActualParityState434 L hS J positions)
    (frame : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J 1 m patterns)
    (hx : x.val.1.val ∈ b654ParitySeedPositions434 lo hi)
    (hy : y.val.1.val ∉ b654ParityIntervalWindow434 J Ck L lo hi) :
    b650IntegerFrameScalar434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns positions q Vs Vb Knu zeta 1 (2*k) x y frame = 0 := by
  have hn : ¬ b650IntegerFrameAllowed434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns positions 1 (2*k) x y frame := by
    intro ha
    exact hy (parity_actual_allowed_frame_target_in_window434
      J m Ck L hL hS patterns k hk positions lo hi x y frame hx ha)
  simp only [b650IntegerFrameScalar434,hn,ite_false]

/-- The SAME zero statement after multiplying by the literal original
psi(n/(Z*D_frame)), without a positivity or regularity condition on psi.
It retains the full frame divisor and therefore applies to the harmonic
cutoff t*psi(t) as well. -/
theorem parity_actual_cutoff_frame_zero_outside434
    (J m : ℕ) (Ck L : ℝ) (hL : Real.exp 1 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
    (k : ℤ) (hk : (k.natAbs:ℝ) ≤ L^Ck)
    (positions : Finset ℤ) (lo hi : ℕ)
    (q : ℝ) (Vs : SourceNativeMemorySG434 20 L hS → ℝ)
    (Vb : sourceNativeOriginalBigType434 20 L → ℝ)
    (Knu : SourcePatternK (SourceNativeMemoryBP434 20 L) J 1 m patterns)
    (zeta Z : ℝ) (psi : ℝ → ℂ)
    (x y : B654ActualParityState434 L hS J positions)
    (frame : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J 1 m patterns)
    (hx : x.val.1.val ∈ b654ParitySeedPositions434 lo hi)
    (hy : y.val.1.val ∉ b654ParityIntervalWindow434 J Ck L lo hi) :
    b650IntegerFrameScalar434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns positions q Vs Vb Knu zeta 1 (2*k) x y frame *
      psi ((x.val.1.val:ℝ)/(Z*(b650NativeFrameD434
        (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
        J 1 m patterns x.val.2 frame:ℝ))) = 0 := by
  rw [parity_actual_frame_scalar_zero_outside434
    J m Ck L hL hS patterns k hk positions lo hi q Vs Vb Knu zeta x y frame hx hy]
  exact zero_mul _

/-- The actual original-psi RAW-plus-comparison matrix has no row
contribution outside the local window from a seed source. The proof
sums the preceding framewise zeros; it does not infer support from the
uncut matrix, whose distinct frame contributions may cancel. -/
theorem parity_actual_cutoff_matrix_zero_outside434
    (L : ℝ) (hL : Real.exp 1 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z Ck : ℝ)
    (k : ℤ) (hk : (k.natAbs:ℝ) ≤ L^Ck)
    (positions : Finset ℤ) (lo hi : ℕ) (psi : ℝ → ℂ)
    (x y : B654ActualParityState434 L hS J positions)
    (hx : x.val.1.val ∈ b654ParitySeedPositions434 lo hi)
    (hy : y.val.1.val ∉ b654ParityIntervalWindow434 J Ck L lo hi) :
    parityActualPsiCutoffMatrix434 L hS J m hmJ Q h xi zeta Z (2*k) positions psi x y = 0 := by
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  change (∑ frame : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
    (SourceNativeMemoryBP434 20 L) J 1 m pats,
    b650IntegerFrameScalar434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m pats positions (1/2:ℝ) (SourceNativeMemorySmallMass434 20 L hS)
      (sourceNativeOriginalVbig434 20 L) Knu zeta 1 (2*k) x y frame *
      psi ((x.val.1.val:ℝ)/(Z*(b650NativeFrameD434
        (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
        J 1 m pats x.val.2 frame:ℝ)))) = 0
  apply Finset.sum_eq_zero
  intro frame hf
  exact parity_actual_cutoff_frame_zero_outside434
    J m Ck L hL hS pats k hk positions lo hi (1/2:ℝ)
    (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
    Knu zeta Z psi x y frame hx hy
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualCarrierTransport -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.SpectralEndpoint Green64Analytic.CorrelationSquare
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 24000

/-- The actual carrier inclusion preserves position and the complete
MemoryIndependentState, including every ordered SMALL and BIG mark. -/
def parityActualCarrierInclusion434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ)
    {U V : Finset ℤ} (hUV : U ⊆ V) :
    B654ActualParityState434 L hS J U → B654ActualParityState434 L hS J V :=
  parityPhysicalCarrierInclusion434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 hUV

theorem parity_actual_carrier_range434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ)
    {U V : Finset ℤ} (hUV : U ⊆ V) (x : B654ActualParityState434 L hS J V) :
    (∃ y, parityActualCarrierInclusion434 L hS J hUV y=x) ↔ x.val.1.val∈U :=
  parity_physical_carrier_range434 _ _ _ _ J 1 hUV x

/-- The actual original-psi kernel is exactly restricted, including
Knu, auxiliary product laws and both original state mass normalizations. -/
theorem parity_actual_psi_matrix_inclusion434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    {U V : Finset ℤ} (hUV : U ⊆ V) (psi : ℝ → ℂ)
    (x y : B654ActualParityState434 L hS J U) :
    parityActualPsiCutoffMatrix434 L hS J m hmJ Q h xi zeta Z k V psi
      (parityActualCarrierInclusion434 L hS J hUV x)
      (parityActualCarrierInclusion434 L hS J hUV y) =
    parityActualPsiCutoffMatrix434 L hS J m hmJ Q h xi zeta Z k U psi x y := rfl

/-- Exact original arithmetic second-vector restriction, retaining its
single sqrt(mu0). No norm or mark-fibre cardinality is introduced. -/
theorem parity_actual_endpoint_inclusion434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ)
    {U V : Finset ℤ} (hUV : U ⊆ V) (G : PrimeSlotCore) (t : ℝ)
    (eta : B654ActualParityState434 L hS J V → ℂ)
    (x : B654ActualParityState434 L hS J U) :
    b657ActualPrimeEndpointVector434 L hS J V G t eta
      (parityActualCarrierInclusion434 L hS J hUV x) =
    b657ActualPrimeEndpointVector434 L hS J U G t
      (fun y => eta (parityActualCarrierInclusion434 L hS J hUV y)) x := rfl

/-- An interval-window inclusion retaining the original radius. -/
theorem parity_interval_window_mono434 (J : ℕ) (Ck L : ℝ)
    (lo hi a b : ℕ) (hlo : a≤lo) (hhi : hi≤b) :
    b654ParityIntervalWindow434 J Ck L lo hi ⊆ b654ParityIntervalWindow434 J Ck L a b := by
  intro n hn
  obtain ⟨hnlo,hnhi⟩ := Finset.mem_Icc.mp hn
  apply Finset.mem_Icc.mpr
  constructor <;> omega

/-- Exact cutoff pairing transport to the local interval window. The
only size inputs are exp(1)<=L and the actual signed shift cap. Locality
is discharged for every frame by the preceding production theorem. -/
theorem parity_actual_cutoff_pairing_transport434
    (L : ℝ) (hL : Real.exp 1 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z Ck : ℝ)
    (k : ℤ) (hk : (k.natAbs:ℝ) ≤ L^Ck) (lo hi : ℕ)
    (V : Finset ℤ) (hUV : b654ParityIntervalWindow434 J Ck L lo hi ⊆ V)
    (psi : ℝ → ℂ) (c : ℤ → ℂ)
    (gV : EuclideanSpace ℂ (B654ActualParityState434 L hS J V))
    (gU : EuclideanSpace ℂ (B654ActualParityState434 L hS J
      (b654ParityIntervalWindow434 J Ck L lo hi)))
    (hg : ∀ x, gV (parityActualCarrierInclusion434 L hS J hUV x)=gU x) :
    inner ℂ (b655ActualParityFirstVector434 L hS J V lo hi c)
      ((parityActualPsiCutoffMatrix434 L hS J m hmJ Q h xi zeta Z (2*k) V psi).toEuclideanLin gV) =
    inner ℂ (b655ActualParityFirstVector434 L hS J
      (b654ParityIntervalWindow434 J Ck L lo hi) lo hi c)
      ((parityActualPsiCutoffMatrix434 L hS J m hmJ Q h xi zeta Z (2*k)
        (b654ParityIntervalWindow434 J Ck L lo hi) psi).toEuclideanLin gU) := by
  let U := b654ParityIntervalWindow434 J Ck L lo hi
  let e := parityActualCarrierInclusion434 L hS J hUV
  let posU : B654ActualParityState434 L hS J U → ℤ := fun x => x.val.1.val
  let posV : B654ActualParityState434 L hS J V → ℤ := fun x => x.val.1.val
  let w : ℂ := Real.sqrt (b657ActualStateMass434 L hS J)
  let KU := parityActualPsiCutoffMatrix434 L hS J m hmJ Q h xi zeta Z (2*k) U psi
  let KV := parityActualPsiCutoffMatrix434 L hS J m hmJ Q h xi zeta Z (2*k) V psi
  have he : Function.Injective e := parity_physical_carrier_injective434 _ _ _ _ J 1 hUV
  have hrow : ∀ x y (_ : Unit), KV (e x) (e y)=KU x y := by
    intro x y t
    exact parity_actual_psi_matrix_inclusion434 L hS J m hmJ Q h xi zeta Z (2*k) hUV psi x y
  have hseed : ∀ x, posV x∈b654ParitySeedPositions434 lo hi → ∃ y,e y=x := by
    intro x hx
    apply (parity_actual_carrier_range434 L hS J hUV x).mpr
    obtain ⟨n,hn,heq⟩ := Finset.mem_image.mp hx
    change posV x ∈ b654ParityIntervalWindow434 J Ck L lo hi
    rw [←heq]
    exact b654_seed_mem_interval_window434 J Ck L lo hi n hn
  have hlocal : ∀ x, posU x∈b654ParitySeedPositions434 lo hi →
      ∀ y, (¬∃ z,e z=y) → ∀ _ : Unit, KV (e x) y=0 := by
    intro x hx y hy t
    have hyU : y.val.1.val∉U := by
      intro hmem
      exact hy ((parity_actual_carrier_range434 L hS J hUV y).mpr hmem)
    exact parity_actual_cutoff_matrix_zero_outside434 L hL hS J m hmJ Q h xi zeta Z Ck
      k hk V lo hi psi (e x) y hx hyU
  have ht := parity_seed_frame_transport434 e he posU posV (fun _ => rfl)
    (b654ParitySeedPositions434 lo hi) w c
    (fun x y (_ : Unit) => KU x y) (fun x y (_ : Unit) => KV x y)
    gU gV hrow hg hseed hlocal
  have hKA : b658FrameMatrix434 (fun x y (_ : Unit) => KU x y)=KU := by
    ext x y
    simp [b658FrameMatrix434]
  have hKB : b658FrameMatrix434 (fun x y (_ : Unit) => KV x y)=KV := by
    ext x y
    simp [b658FrameMatrix434]
  rw [hKA,hKB] at ht
  exact ht

/-- Actual source parity is preserved definitionally at both endpoints.
The conclusion has no independent local multiplier compatibility premise. -/
theorem parity_actual_parity_pairing_transport434
    (L : ℝ) (hL : Real.exp 1 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z Ck : ℝ)
    (k : ℤ) (hk : (k.natAbs:ℝ) ≤ L^Ck) (lo hi : ℕ)
    (V : Finset ℤ) (hUV : b654ParityIntervalWindow434 J Ck L lo hi ⊆ V)
    (psi : ℝ → ℂ) (c : ℤ → ℂ) (G : PrimeSlotCore) (t : ℝ) (tw : Bool) :
    inner ℂ (b655ActualParityFirstVector434 L hS J V lo hi c)
      ((parityActualPsiCutoffMatrix434 L hS J m hmJ Q h xi zeta Z (2*k) V psi).toEuclideanLin
        (b657ActualPrimeEndpointVector434 L hS J V G t (fun x =>
          (groupSign (sourceOriginalPAllActualBands 20 L) tw x.val.1.val.toNat:ℂ)))) =
    inner ℂ (b655ActualParityFirstVector434 L hS J
      (b654ParityIntervalWindow434 J Ck L lo hi) lo hi c)
      ((parityActualPsiCutoffMatrix434 L hS J m hmJ Q h xi zeta Z (2*k)
        (b654ParityIntervalWindow434 J Ck L lo hi) psi).toEuclideanLin
        (b657ActualPrimeEndpointVector434 L hS J
          (b654ParityIntervalWindow434 J Ck L lo hi) G t (fun x =>
          (groupSign (sourceOriginalPAllActualBands 20 L) tw x.val.1.val.toNat:ℂ)))) := by
  exact parity_actual_cutoff_pairing_transport434 L hL hS J m hmJ Q h xi zeta Z Ck
    k hk lo hi V hUV psi c _ _ (fun _ => rfl)
end Green64Analytic.SourceBlockSieve

end

end

/-! ## HarmonicAssembly -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 24000

/-- Independently defined original finite harmonic physical functional.
This is ONE global-carrier pairing with the literal c_1 coefficient,
original full-frame psi matrix and original same-parity second endpoint.
It is not defined by a dyadic sum. -/
def parityHarmonicPhysical434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z Ck : ℝ) (k : ℤ) (T : ℕ)
    (Ecore Gcore : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) : ℂ :=
  let V := b654ParityIntervalWindow434 J Ck L 1 (2^T)
  inner ℂ (b655ActualParityFirstVector434 L hS J V 1 (2^T)
    (b659ActualParityRootCoefficient434 L hS J Ecore t1 tw 1 Z v))
    ((parityActualPsiCutoffMatrix434 L hS J m hmJ Q h xi zeta Z (2*k) V psi).toEuclideanLin
      (b657ActualPrimeEndpointVector434 L hS J V Gcore t2 (fun x =>
        (groupSign (sourceOriginalPAllActualBands 20 L) tw x.val.1.val.toNat:ℂ))))

/-- Exact local interval carrier inclusion for every retained dyad. -/
theorem parity_dyadic_window_subset434 (J : ℕ) (Ck L : ℝ) (T j : ℕ) (hj : j<T) :
    b654ParityIntervalWindow434 J Ck L (2^j) (2*2^j) ⊆
      b654ParityIntervalWindow434 J Ck L 1 (2^T) := by
  have hlo : 1 ≤ (2:ℕ)^j := by
    have hp : 0 < (2:ℕ)^j := by positivity
    omega
  have hhi : 2*2^j ≤ (2:ℕ)^T := by
    calc
      2*2^j = (2:ℕ)^(j+1) := by ring
      _ ≤ (2:ℕ)^T := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact parity_interval_window_mono434 J Ck L (2^j) (2*2^j) 1 (2^T) hlo hhi

/-- Exact full harmonic assembly. Each local physical pairing is computed
on its OWN complete interval carrier. Every frame is retained, and no
boundary estimate, mark count or second normalization appears. -/
theorem parity_harmonic_physical_dyadic434
    (L : ℝ) (hL : Real.exp 1 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z Ck : ℝ)
    (k : ℤ) (hk : (k.natAbs:ℝ) ≤ L^Ck) (T : ℕ)
    (Ecore Gcore : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) :
    parityHarmonicPhysical434 L hS J m hmJ Q h xi zeta Z Ck k T Ecore Gcore t1 t2 tw v psi =
      ∑ j ∈ Finset.range T, ((1/((2^j:ℕ):ℝ):ℝ):ℂ) *
        inner ℂ (b655ActualParityFirstVector434 L hS J
          (b654ParityIntervalWindow434 J Ck L (2^j) (2*2^j)) (2^j) (2*2^j)
          (b659ActualParityRootCoefficient434 L hS J Ecore t1 tw (2^j) Z v))
          ((parityActualPsiCutoffMatrix434 L hS J m hmJ Q h xi zeta Z (2*k)
            (b654ParityIntervalWindow434 J Ck L (2^j) (2*2^j)) psi).toEuclideanLin
            (b657ActualPrimeEndpointVector434 L hS J
              (b654ParityIntervalWindow434 J Ck L (2^j) (2*2^j)) Gcore t2 (fun x =>
              (groupSign (sourceOriginalPAllActualBands 20 L) tw x.val.1.val.toNat:ℂ)))) := by
  unfold parityHarmonicPhysical434
  dsimp only
  rw [parity_actual_harmonic_pairing_dyadic_fixed_carrier434]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact parity_actual_parity_pairing_transport434 L hL hS J m hmJ Q h xi zeta Z Ck
    k hk (2^j) (2*2^j) (b654ParityIntervalWindow434 J Ck L 1 (2^T))
    (parity_dyadic_window_subset434 J Ck L T j (Finset.mem_range.mp hj)) psi
    (b659ActualParityRootCoefficient434 L hS J Ecore t1 tw (2^j) Z v) Gcore t2 tw

/-- The source normalization keeps exactly ONE exterior Z. -/
theorem parity_Z_harmonic_physical_dyadic434
    (L : ℝ) (hL : Real.exp 1 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z Ck : ℝ)
    (k : ℤ) (hk : (k.natAbs:ℝ) ≤ L^Ck) (T : ℕ)
    (Ecore Gcore : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) :
    (Z:ℂ)*parityHarmonicPhysical434 L hS J m hmJ Q h xi zeta Z Ck k T Ecore Gcore t1 t2 tw v psi =
      ∑ j ∈ Finset.range T, ((Z/((2^j:ℕ):ℝ):ℝ):ℂ) *
        inner ℂ (b655ActualParityFirstVector434 L hS J
          (b654ParityIntervalWindow434 J Ck L (2^j) (2*2^j)) (2^j) (2*2^j)
          (b659ActualParityRootCoefficient434 L hS J Ecore t1 tw (2^j) Z v))
          ((parityActualPsiCutoffMatrix434 L hS J m hmJ Q h xi zeta Z (2*k)
            (b654ParityIntervalWindow434 J Ck L (2^j) (2*2^j)) psi).toEuclideanLin
            (b657ActualPrimeEndpointVector434 L hS J
              (b654ParityIntervalWindow434 J Ck L (2^j) (2*2^j)) Gcore t2 (fun x =>
              (groupSign (sourceOriginalPAllActualBands 20 L) tw x.val.1.val.toNat:ℂ)))) := by
  rw [parity_harmonic_physical_dyadic434 L hL hS J m hmJ Q h xi zeta Z Ck k hk]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  ring
end Green64Analytic.Parity

end

end

/-! ## HarmonicSaving -/

section

open Filter Real
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64FullPhysicalE Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 26000

/-- Full harmonic dyadic saving for the independently defined global
physical RAW-plus-comparison functional. The local precision A+2 is
requested BEFORE the one operator tuple is chosen. There is exactly one
exterior Z. The same original P-parity, complete marked states, both
reciprocal masses, source phases and harmonic cutoff t*psi(t) are retained.
No dyadic identity, locality or summation estimate is an input premise. -/
theorem parity_eventually_actual_harmonic_physical_saving434
    (A Czeta Ck Cpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hA : 0 < A) (hCk : 0 ≤ Ck)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j) :
    ∃ (m : ℕ) (D HH : ℝ) (Cq Cxi J : ℕ) (hmJ : m ≤ J),
      1 ≤ m ∧ 0 ≤ D ∧ 0 ≤ HH ∧
      ∀ (S beta gamma CZ : ℝ), 0 < S → 0 < beta → 0 < gamma → 0 ≤ CZ →
      ∀ᶠ L : ℝ in atTop,
      let Q : ℕ := Nat.ceil (4*L^(D+1))
      let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
      let xi : ℝ := L^(-(Cxi:ℝ))
      1 < L ∧ 0 < Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0 < h ∧ h+h ≤ 1 ∧
      0 < xi ∧ xi⁻¹ ≤ L^Cxi ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (psi : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ psi)
        (hSupport : ∀ x, psi x ≠ 0 → (1/64:ℝ) ≤ x ∧ x ≤ 64),
      sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)) →
      ∀ (xi3 : ℝ), |xi3| ≤ L^Czeta → ∀ (k : ℤ), k ≠ 0 →
        (k.natAbs:ℝ) ≤ L^Ck →
      ∀ (prime : Bool) (l u : ℕ), Real.exp (beta*L) ≤ (l:ℝ) →
      ∀ (r d : ℕ), 1 ≤ r → ∀ (b : Fin (d+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
      let F := sourceNativePrimeCore r d L b slot δ ξ K
        (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
      ∀ xi1 xi2 rho sigma : ℝ,
      let Ecore := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
      let Gcore := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
      ∀ (tw : Bool) (Z : ℝ),
        Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ‖(Z:ℂ)*parityHarmonicPhysical434 L hFamily J m hmJ Q h xi (-xi3) Z Ck k
          (parityDyadicDepth434 L) Ecore Gcore (-(rho+xi3)) (-rho) tw 0
          (fun t => (t:ℂ)*psi t)‖ ≤ Z*L^(-A) := by
  have hE : 0 < A+2 := by linarith
  obtain ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,hDyads⟩ :=
    parity_eventually_actual_normalized_physical_dyad434
      (A+2) Czeta Ck Cpsi Kpsi hE hCk hCpsi hKpsi
  refine ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,?_⟩
  intro S beta gamma CZ hS hbeta hgamma hCZ
  filter_upwards [hDyads S beta gamma CZ hS hbeta hgamma hCZ,
    eventually_ge_atTop (5:ℝ),eventually_ge_atTop (Real.exp 1)] with L hSave hL5 hLexp
  dsimp only at hSave ⊢
  obtain ⟨hL,hQ,hQc,hh,hh1,hxi,hxic,hFamily0,hSave⟩ := hSave
  refine ⟨hL,hQ,hQc,hh,hh1,hxi,hxic,hFamily0,?_⟩
  intro hFamily psi hSmooth hSupport hReg xi3 hxi3 k hk hkBound prime l u hlow
    r d hr b slot δ ξ K q chi s0 s1 xi1 xi2 rho sigma tw Z hZlo hZhi
  have hLp : 0<L := by linarith
  have hZp : 0<Z :=
    (mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  rw [parity_Z_harmonic_physical_dyadic434 L hLexp hFamily J m hmJ
    (Nat.ceil (4*L^(D+1))) (Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ))
    (L^(-(Cxi:ℝ))) (-xi3) Z Ck k hkBound]
  apply parity_dyadic_sum_loss434 A L Z hL5 hZp.le
  intro j hj
  exact hSave hFamily psi hSmooth hSupport hReg xi3 hxi3 k hk hkBound
    prime l u hlow r d hr b slot δ ξ K q chi s0 s1 xi1 xi2 rho sigma tw (2^j) Z hZlo hZhi
end Green64Analytic.Parity

end

end

/-! ## HarmonicStabilization -/

section

open Filter Real Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 22000000
set_option maxRecDepth 26000

/-- Original physical partial harmonic functional at an arbitrary natural
upper cutoff M. The full carrier, all marked states, original frame matrix
and exact c_1 arithmetic endpoint are independent of a dyadic partition. -/
def parityHarmonicPhysicalCut434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z Ck : ℝ) (k : ℤ) (M : ℕ)
    (Ecore Gcore : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) : ℂ :=
  let V := b654ParityIntervalWindow434 J Ck L 1 M
  inner ℂ (b655ActualParityFirstVector434 L hS J V 1 M
    (b659ActualParityRootCoefficient434 L hS J Ecore t1 tw 1 Z v))
    ((parityActualPsiCutoffMatrix434 L hS J m hmJ Q h xi zeta Z (2*k) V psi).toEuclideanLin
      (b657ActualPrimeEndpointVector434 L hS J V Gcore t2 (fun x =>
        (groupSign (sourceOriginalPAllActualBands 20 L) tw x.val.1.val.toNat:ℂ))))

/-- The unrestricted positive harmonic physical functional is defined by
its original arbitrary-cutoff partial functionals, with no dyadic sum in
its definition. The next theorem proves exact eventual constancy, hence
existence and uniqueness of this limit in the actual source domain. -/
def parityOriginalHarmonicPhysical434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z Ck : ℝ) (k : ℤ)
    (Ecore Gcore : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) : ℂ :=
  Filter.limUnder (atTop : Filter ℕ) (fun M =>
    parityHarmonicPhysicalCut434 L hS J m hmJ Q h xi zeta Z Ck k M Ecore Gcore t1 t2 tw v psi)

/-- Every larger original cutoff gives EXACTLY the controlled harmonic
functional H_T. First remove the outer seed tail frame by frame, then
transport the complete endpoint carrier using the proved radius R. -/
theorem parity_eventually_harmonic_cut_stabilizes434
    (J : ℕ) (Ck CZ : ℝ) (hCk : 0 ≤ Ck) :
    ∀ᶠ L : ℝ in atTop, Real.exp 1 ≤ L ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ),
      (k.natAbs:ℝ) ≤ L^Ck → 0<Z → Z≤Real.exp L*L^CZ →
    ∀ (Ecore Gcore : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ),
      (∀ x, psi x≠0 → (1/64:ℝ)≤x ∧ x≤64) →
    ∀ M : ℕ, parityDyadicLimit434 L≤M →
      parityHarmonicPhysicalCut434 L hS J m hmJ Q h xi zeta Z Ck k M
        Ecore Gcore t1 t2 tw v psi =
      parityHarmonicPhysical434 L hS J m hmJ Q h xi zeta Z Ck k
        (parityDyadicDepth434 L) Ecore Gcore t1 t2 tw v psi := by
  filter_upwards [parity_eventually_actual_cutoff_seed_truncation434 J Ck CZ hCk]
    with L hTrunc
  refine ⟨hTrunc.1,?_⟩
  intro hS m hmJ Q h xi zeta Z k hk hZ hZhi Ecore Gcore t1 t2 tw v psi hpsi M hM
  let V := b654ParityIntervalWindow434 J Ck L 1 M
  let c := b659ActualParityRootCoefficient434 L hS J Ecore t1 tw 1 Z v
  let gV := b657ActualPrimeEndpointVector434 L hS J V Gcore t2 (fun x =>
    (groupSign (sourceOriginalPAllActualBands 20 L) tw x.val.1.val.toNat:ℂ))
  have h0 := hTrunc.2 hS m hmJ Q h xi zeta Z k V M hM hZ hZhi psi hpsi c gV
  have hUV : b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)⊆V :=
    parity_interval_window_mono434 J Ck L 1 (parityDyadicLimit434 L) 1 M le_rfl hM
  have h1 := parity_actual_parity_pairing_transport434 L hTrunc.1 hS J m hmJ
    Q h xi zeta Z Ck k hk 1 (parityDyadicLimit434 L) V hUV psi c Gcore t2 tw
  exact h0.trans h1

/-- The independently defined untruncated physical functional equals the
controlled H_T. This proves its limit exists; it is not a definition by
the desired dyadic decomposition. -/
theorem parity_eventually_original_harmonic_eq_controlled434
    (J : ℕ) (Ck CZ : ℝ) (hCk : 0 ≤ Ck) :
    ∀ᶠ L : ℝ in atTop, Real.exp 1 ≤ L ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ),
      (k.natAbs:ℝ) ≤ L^Ck → 0<Z → Z≤Real.exp L*L^CZ →
    ∀ (Ecore Gcore : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ),
      (∀ x, psi x≠0 → (1/64:ℝ)≤x ∧ x≤64) →
      parityOriginalHarmonicPhysical434 L hS J m hmJ Q h xi zeta Z Ck k
        Ecore Gcore t1 t2 tw v psi =
      parityHarmonicPhysical434 L hS J m hmJ Q h xi zeta Z Ck k
        (parityDyadicDepth434 L) Ecore Gcore t1 t2 tw v psi := by
  filter_upwards [parity_eventually_harmonic_cut_stabilizes434 J Ck CZ hCk]
    with L hStab
  refine ⟨hStab.1,?_⟩
  intro hS m hmJ Q h xi zeta Z k hk hZ hZhi Ecore Gcore t1 t2 tw v psi hpsi
  have he : (fun M : ℕ => parityHarmonicPhysicalCut434 L hS J m hmJ Q h xi zeta Z Ck k M
      Ecore Gcore t1 t2 tw v psi) =ᶠ[atTop]
      (fun _ => parityHarmonicPhysical434 L hS J m hmJ Q h xi zeta Z Ck k
        (parityDyadicDepth434 L) Ecore Gcore t1 t2 tw v psi) := by
    filter_upwards [eventually_ge_atTop (parityDyadicLimit434 L)] with M hM
    exact hStab.2 hS m hmJ Q h xi zeta Z k hk hZ hZhi Ecore Gcore t1 t2 tw v psi hpsi M hM
  unfold parityOriginalHarmonicPhysical434
  apply Filter.Tendsto.limUnder_eq
  exact tendsto_const_nhds.congr' he.symm
end Green64Analytic.Parity

end

end

/-! ## OriginalHarmonicSaving -/

section

open Filter Real
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64FullPhysicalE Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 26000000
set_option maxRecDepth 28000

/-- The independently defined controlled functional equals the literal
original full frame sum with exactly mu0, the harmonic 1/n coefficient,
all ordered marks, shared/free products, actual Knu and same P-parity. -/
theorem parity_controlled_harmonic_eq_frames434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z Ck : ℝ) (k : ℤ) (T : ℕ)
    (Ecore Gcore : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) :
    parityHarmonicPhysical434 L hS J m hmJ Q h xi zeta Z Ck k T
      Ecore Gcore t1 t2 tw v psi =
    parityActualHarmonicFrameSum434 L hS J m hmJ Q h xi zeta Z k
      (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T)
      Ecore Gcore t1 t2 tw v psi := by
  exact parity_actual_harmonic_pairing_eq_frames434 L hS J m hmJ Q h xi zeta Z k
    (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) Ecore Gcore t1 t2 tw v psi

/-- The ORIGINAL positive harmonic physical functional, defined from
arbitrary natural-cutoff partial frame pairings, has arbitrary logarithmic
saving with one exterior Z. Exact eventual stabilization and full carrier
transport are proved internally. The local precision A+2 precedes the
operator tuple. This is RAW-plus-comparison, before restoration and signed
comparison subtraction; it is not E4.1, Type II or Green64. -/
theorem parity_eventually_original_harmonic_physical_saving434
    (A Czeta Ck Cpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hA : 0 < A) (hCk : 0 ≤ Ck)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j) :
    ∃ (m : ℕ) (D HH : ℝ) (Cq Cxi J : ℕ) (hmJ : m ≤ J),
      1 ≤ m ∧ 0 ≤ D ∧ 0 ≤ HH ∧
      ∀ (S beta gamma CZ : ℝ), 0 < S → 0 < beta → 0 < gamma → 0 ≤ CZ →
      ∀ᶠ L : ℝ in atTop,
      let Q : ℕ := Nat.ceil (4*L^(D+1))
      let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
      let xi : ℝ := L^(-(Cxi:ℝ))
      1 < L ∧ 0 < Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0 < h ∧ h+h ≤ 1 ∧
      0 < xi ∧ xi⁻¹ ≤ L^Cxi ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (psi : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ psi)
        (hSupport : ∀ x, psi x ≠ 0 → (1/64:ℝ) ≤ x ∧ x ≤ 64),
      sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)) →
      ∀ (xi3 : ℝ), |xi3| ≤ L^Czeta → ∀ (k : ℤ), k ≠ 0 →
        (k.natAbs:ℝ) ≤ L^Ck →
      ∀ (prime : Bool) (l u : ℕ), Real.exp (beta*L) ≤ (l:ℝ) →
      ∀ (r d : ℕ), 1 ≤ r → ∀ (b : Fin (d+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
      let F := sourceNativePrimeCore r d L b slot δ ξ K
        (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
      ∀ xi1 xi2 rho sigma : ℝ,
      let Ecore := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
      let Gcore := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
      ∀ (tw : Bool) (Z : ℝ),
        Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ‖(Z:ℂ)*parityOriginalHarmonicPhysical434 L hFamily J m hmJ Q h xi (-xi3) Z Ck k
          Ecore Gcore (-(rho+xi3)) (-rho) tw 0
          (fun t => (t:ℂ)*psi t)‖ ≤ Z*L^(-A) := by
  obtain ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,hControlled⟩ :=
    parity_eventually_actual_harmonic_physical_saving434 A Czeta Ck Cpsi Kpsi hA hCk hCpsi hKpsi
  refine ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,?_⟩
  intro S beta gamma CZ hS hbeta hgamma hCZ
  filter_upwards [hControlled S beta gamma CZ hS hbeta hgamma hCZ,
    parity_eventually_original_harmonic_eq_controlled434 J Ck CZ hCk]
    with L hSave hOriginal
  dsimp only at hSave ⊢
  obtain ⟨hL,hQ,hQc,hh,hh1,hxi,hxic,hFamily0,hSave⟩ := hSave
  refine ⟨hL,hQ,hQc,hh,hh1,hxi,hxic,hFamily0,?_⟩
  intro hFamily psi hSmooth hSupport hReg xi3 hxi3 k hk hkBound prime l u hlow
    r d hr b slot δ ξ K q chi s0 s1 xi1 xi2 rho sigma tw Z hZlo hZhi
  have hLp : 0<L := by linarith
  have hZp : 0<Z :=
    (mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hSupportH : ∀ (t : ℝ), (t:ℂ)*psi t≠0 → (1/64:ℝ)≤t ∧ t≤64 := by
    intro t ht
    apply hSupport t
    intro hz
    exact ht (by rw [hz,mul_zero])
  let F := sourceNativePrimeCore r d L b slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let Ecore := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let Gcore := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  have he := hOriginal.2 hFamily m hmJ (Nat.ceil (4*L^(D+1)))
    (Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)) (L^(-(Cxi:ℝ))) (-xi3) Z k hkBound hZp hZhi
    Ecore Gcore (-(rho+xi3)) (-rho) tw 0 (fun t => (t:ℂ)*psi t) hSupportH
  rw [he]
  exact hSave hFamily psi hSmooth hSupport hReg xi3 hxi3 k hk hkBound
    prime l u hlow r d hr b slot δ ξ K q chi s0 s1 xi1 xi2 rho sigma tw Z hZlo hZhi
end Green64Analytic.Parity

end

end

/-! ## FrameStripping -/

section

open scoped BigOperators Classical
noncomputable section

namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 24000
set_option linter.unusedSectionVars false

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The literal product of EVERY shared SMALL and BIG slot, evaluated after
the source endpoint permutations of the original primitive frame. There is
no auxiliary factor and no replacement of the labelled product by an image. -/
def parityFrameSharedD434
    (x : MemoryIndependentState SP sm BP bm J ell)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) : ℕ :=
  (∏ g : SG, ∏ j ∈ sourceSmallShared J ell g,
    sm g (Green64SmallHaar.marks (sm g) (J+ell) (x.1 g) (f.2.2.2.1 g j))) *
  (∏ g : BG, ∏ j ∈ sourceBigShared J ell m (patterns f.1.1) g,
    bm g (Green64SmallHaar.marks (bm g) (J+ell) (x.2 g) (f.2.1 g j)))

/-- The complete auxiliary product, with every free slot retained. Equal
draws in different slots multiply repeatedly; no distinct-support operation
occurs. Its value is independent of the physical endpoint. -/
def parityFrameAuxD434
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) : ℕ :=
  ∏ g : BG, ∏ j : ↥((patterns f.1.1).free g), bm g (f.1.2 g j)

/-- Exact factorization of the original complete physical frame divisor. -/
theorem parity_frame_D_factor434
    (x : MemoryIndependentState SP sm BP bm J ell)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) :
    b650NativeFrameD434 SP sm BP bm J ell m patterns x f =
      parityFrameSharedD434 SP sm BP bm J ell m patterns x f *
      parityFrameAuxD434 BP bm J ell m patterns f := by
  unfold b650NativeFrameD434 memoryIndependentD parityFrameSharedD434 parityFrameAuxD434
  rw [Finset.prod_mul_distrib]
  exact (mul_assoc _ _ _).symm

theorem parity_frame_shared_D_pos434
    (x : MemoryIndependentState SP sm BP bm J ell)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) :
    0 < parityFrameSharedD434 SP sm BP bm J ell m patterns x f := by
  unfold parityFrameSharedD434
  exact mul_pos
    (Finset.prod_pos (fun g _ => Finset.prod_pos (fun j _ => NeZero.pos _)))
    (Finset.prod_pos (fun g _ => Finset.prod_pos (fun j _ => NeZero.pos _)))

theorem parity_frame_aux_D_pos434
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) :
    0 < parityFrameAuxD434 BP bm J ell m patterns f := by
  unfold parityFrameAuxD434
  exact Finset.prod_pos (fun g _ => Finset.prod_pos (fun j _ => NeZero.pos _))

/-- The shared factor is the same at the target with reversed endpoint
permutations. This uses the literal shared-label guard, not a clean event. -/
theorem parity_frame_shared_D_reverse434
    (x y : MemoryIndependentState SP sm BP bm J ell)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns)
    (hshare : b650NativeFrameShares434 SP sm BP bm J ell m patterns x y f) :
    parityFrameSharedD434 SP sm BP bm J ell m patterns y
      (b650SwapFrame434 BP J ell m patterns f) =
    parityFrameSharedD434 SP sm BP bm J ell m patterns x f := by
  unfold parityFrameSharedD434 b650SwapFrame434
  dsimp only
  congr 1
  · apply Finset.prod_congr rfl
    intro g hg
    apply Finset.prod_congr rfl
    intro j hj
    rw [hshare.1 g j hj]
  · apply Finset.prod_congr rfl
    intro g hg
    apply Finset.prod_congr rfl
    intro j hj
    rw [hshare.2 g j hj]

/-- Each shared product is a subproduct of the complete ordered mark product.
All endpoint permutations are bijections, so no factorial or loss of slots
appears. This step needs no arithmetic coprimality assumption. -/
theorem parity_frame_shared_dvd_full_marks434
    (positions : Finset ℤ)
    (x : B650IntegerPhysicalState434 SP sm BP bm J ell positions)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) :
    parityFrameSharedD434 SP sm BP bm J ell m patterns x.val.2 f ∣
      b657OrderedMarkProduct434 SP sm BP bm (J+ell)
        (b657PhysicalMarkReadout434 SP sm BP bm J ell positions x) := by
  have hs (g : SG) :
      (∏ j ∈ sourceSmallShared J ell g,
        sm g (Green64SmallHaar.marks (sm g) (J+ell) (x.val.2.1 g) (f.2.2.2.1 g j))) ∣
      ∏ j : Fin (J+ell),
        sm g (Green64SmallHaar.marks (sm g) (J+ell) (x.val.2.1 g) j) := by
    have hh := Finset.prod_dvd_prod_of_subset
      (sourceSmallShared J ell g) Finset.univ
      (fun j => sm g (Green64SmallHaar.marks (sm g) (J+ell)
        (x.val.2.1 g) (f.2.2.2.1 g j))) (Finset.subset_univ _)
    rw [Equiv.prod_comp (f.2.2.2.1 g) (fun j =>
      sm g (Green64SmallHaar.marks (sm g) (J+ell) (x.val.2.1 g) j))] at hh
    exact hh
  have hb (g : BG) :
      (∏ j ∈ sourceBigShared J ell m (patterns f.1.1) g,
        bm g (Green64SmallHaar.marks (bm g) (J+ell) (x.val.2.2 g) (f.2.1 g j))) ∣
      ∏ j : Fin (J+ell),
        bm g (Green64SmallHaar.marks (bm g) (J+ell) (x.val.2.2 g) j) := by
    have hh := Finset.prod_dvd_prod_of_subset
      (sourceBigShared J ell m (patterns f.1.1) g) Finset.univ
      (fun j => bm g (Green64SmallHaar.marks (bm g) (J+ell)
        (x.val.2.2 g) (f.2.1 g j))) (Finset.subset_univ _)
    rw [Equiv.prod_comp (f.2.1 g) (fun j =>
      bm g (Green64SmallHaar.marks (bm g) (J+ell) (x.val.2.2 g) j))] at hh
    exact hh
  unfold parityFrameSharedD434 b657OrderedMarkProduct434 b657PhysicalMarkReadout434
  exact Nat.mul_dvd_mul
    (Finset.prod_dvd_prod_of_dvd _ _ (fun g _ => hs g))
    (Finset.prod_dvd_prod_of_dvd _ _ (fun g _ => hb g))
end Green64FullPhysicalE

namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 24000

/-- Signed extension of the actual B657 complete mark divisibility theorem.
The same actual prime-band disjointness and ordered-label injections prove
the product divides |n|, hence n; no positivity premise is introduced. -/
theorem parity_actual_full_mark_product_signed_divides434
    (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (positions : Finset ℤ) (x : B654ActualParityState434 L hS J positions) :
    (b657ActualMarkProduct434 L hS J positions x : ℤ) ∣ x.val.1.val := by
  let s := b657PhysicalMarkReadout434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 positions x
  let p := b657MarkSlotPrime434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) (J+1) s
  have hp (t) : (p t).Prime :=
    (b638_actual_full_P_range434 L hL.le (p t)
      (b657_actual_mark_slot_mem434 L hL hS (J+1) s t)).1
  let hm := b650IntegerStateMarksEquiv434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 x.val.1.val
    ⟨x.val.2,x.property⟩
  have hd : ∀ t, p t ∣ x.val.1.val.natAbs := by
    intro t
    rcases t with ⟨g,j⟩ | ⟨g,j⟩
    · exact Int.natCast_dvd.mp ((hm.1 g).property.2 j)
    · exact Int.natCast_dvd.mp ((hm.2 g).property.2 j)
  apply Int.natCast_dvd.mpr
  change b657OrderedMarkProduct434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) (J+1) s ∣ x.val.1.val.natAbs
  rw [b657_mark_product_eq_slots434]
  exact b657_distinct_prime_product_divides434 p hp
    (b657_actual_mark_slots_injective434 L hL hS (J+1) s) x.val.1.val.natAbs hd

/-- EVERY actual shared slot divides the same physical integer, including
the distinguished SMALL group. The complete shared product divides n by
the already proved full marked-product theorem, without a clean event. -/
theorem parity_actual_frame_shared_divides434
    (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
    (positions : Finset ℤ) (x : B654ActualParityState434 L hS J positions)
    (f : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J 1 m patterns) :
    (parityFrameSharedD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x.val.2 f : ℤ) ∣ x.val.1.val := by
  have hsub := parity_frame_shared_dvd_full_marks434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
    J 1 m patterns positions x f
  have hcast :
      (parityFrameSharedD434
        (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
        J 1 m patterns x.val.2 f : ℤ) ∣
      (b657ActualMarkProduct434 L hS J positions x : ℤ) := by
    exact_mod_cast hsub
  exact hcast.trans (parity_actual_full_mark_product_signed_divides434 L hL hS J positions x)

/-- Exact first physical-to-stripped step for every actual r20 frame.
Both endpoints are divided by the SAME full shared product. The original
guard has shift 2k; its quotient shift is precisely 2k D_C, for either
sign of k and for arbitrary signed physical positions. -/
theorem parity_actual_allowed_frame_quotients434
    (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
    (positions : Finset ℤ) (k : ℤ)
    (x y : B654ActualParityState434 L hS J positions)
    (f : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J 1 m patterns)
    (hallowed : b650IntegerFrameAllowed434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns positions 1 (2*k) x y f) :
    let dR := parityFrameSharedD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x.val.2 f
    let dC := parityFrameAuxD434
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m patterns f
    let w : ℤ := x.val.1.val / (dR : ℤ)
    let wp : ℤ := y.val.1.val / (dR : ℤ)
    x.val.1.val = (dR : ℤ)*w ∧
    y.val.1.val = (dR : ℤ)*wp ∧
    wp = w + 2*k*(dC : ℤ) := by
  let dR := parityFrameSharedD434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
    J 1 m patterns x.val.2 f
  let dC := parityFrameAuxD434
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m patterns f
  have hdR : (0:ℤ) < dR := by
    exact_mod_cast parity_frame_shared_D_pos434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x.val.2 f
  have hdvd : (dR : ℤ) ∣ x.val.1.val :=
    parity_actual_frame_shared_divides434 L hL hS J m patterns positions x f
  have hx : x.val.1.val = (dR : ℤ)*(x.val.1.val/(dR:ℤ)) :=
    (Int.mul_ediv_cancel_of_dvd hdvd).symm
  have hfactor :
      (b650NativeFrameD434
        (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
        J 1 m patterns x.val.2 f : ℤ) = (dR:ℤ)*(dC:ℤ) := by
    exact_mod_cast parity_frame_D_factor434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x.val.2 f
  have hstep := hallowed.2.2.2.2
  rw [one_mul,hfactor] at hstep
  have hy : y.val.1.val = (dR:ℤ)*(x.val.1.val/(dR:ℤ)+2*k*(dC:ℤ)) := by
    calc
      _ = x.val.1.val + 2*k*((dR:ℤ)*(dC:ℤ)) := hstep
      _ = (dR:ℤ)*(x.val.1.val/(dR:ℤ)) + 2*k*((dR:ℤ)*(dC:ℤ)) :=
        congrArg (fun n : ℤ => n + 2*k*((dR:ℤ)*(dC:ℤ))) hx
      _ = _ := by ring
  have hquot : y.val.1.val/(dR:ℤ) = x.val.1.val/(dR:ℤ)+2*k*(dC:ℤ) := by
    rw [hy, Int.mul_ediv_cancel_left _ (ne_of_gt hdR)]
  dsimp only
  exact ⟨hx,by rw [hquot]; exact hy,hquot⟩

/-- RAW has an empty auxiliary slot family, hence D_C=1. This theorem says
nothing of the sort about D_R: RAW retains all original shared marks. -/
theorem parity_actual_RAW_frame_aux_D_one434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (f : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J 1 m
      (sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
        J m hmJ))
    (hraw : f.1.1 = none) :
    parityFrameAuxD434 (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m
      (sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
        J m hmJ) f = 1 := by
  unfold parityFrameAuxD434
  apply Finset.prod_eq_one
  intro g hg
  have hempty :
      ((sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
        J m hmJ f.1.1).free g) = ∅ := by
    rw [hraw]
    rfl
  have : IsEmpty ↥((sourceOriginalMemoryRawComparisonPattern434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
      J m hmJ f.1.1).free g) :=
    ⟨fun j => by simpa only [hempty,Finset.notMem_empty] using j.property⟩
  exact Fintype.prod_empty _

/-- Nonzero original cutoff gives a positive stripped source integer. It
uses the original [1/64,64] support, the complete frame divisor, and Z>0;
no condition on the sign of k or on the stripped target is inferred. -/
theorem parity_actual_frame_cutoff_source_quotient_pos434
    (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
    (positions : Finset ℤ) (x : B654ActualParityState434 L hS J positions)
    (f : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J 1 m patterns)
    (Z : ℝ) (hZ : 0 < Z) (psi : ℝ → ℂ)
    (hSupport : ∀ u, psi u ≠ 0 → (1/64:ℝ) ≤ u ∧ u ≤ 64)
    (hpsi : psi ((x.val.1.val:ℝ)/(Z*(b650NativeFrameD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x.val.2 f:ℝ))) ≠ 0) :
    0 < x.val.1.val / (parityFrameSharedD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x.val.2 f : ℤ) := by
  let dR := parityFrameSharedD434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
    J 1 m patterns x.val.2 f
  have hdR := parity_frame_shared_D_pos434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
    J 1 m patterns x.val.2 f
  have hdC := parity_frame_aux_D_pos434
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m patterns f
  have hD : (0:ℝ) < b650NativeFrameD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x.val.2 f := by
    rw [parity_frame_D_factor434]
    exact_mod_cast Nat.mul_pos hdR hdC
  have hden := mul_pos hZ hD
  have hnReal : (0:ℝ) < x.val.1.val :=
    (mul_pos (by norm_num : (0:ℝ)<1/64) hden).trans_le
      ((le_div_iff₀ hden).mp (hSupport _ hpsi).1)
  have hn : 0 < x.val.1.val := by exact_mod_cast hnReal
  apply Int.ediv_pos_of_pos_of_dvd hn
  · exact_mod_cast hdR.le
  · exact parity_actual_frame_shared_divides434 L hL hS J m patterns positions x f
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualHarmonicError -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 24000

/-- The literal repeated auxiliary product is bounded by the already proved
physical window. No auxiliary draw, group or endpoint normalization changes. -/
theorem parity_actual_frame_aux_window434
    (L : ℝ) (hL : Real.exp 1 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
    (x : MemoryIndependentState
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1)
    (f : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J 1 m patterns) :
    (parityFrameAuxD434 (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns f : ℝ) ≤ (b651ParityWindowSize434 J 0 L : ℝ) := by
  have hshared := parity_frame_shared_D_pos434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
    J 1 m patterns x f
  have hfactor := parity_frame_D_factor434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
    J 1 m patterns x f
  have hsub : parityFrameAuxD434 (SourceNativeMemoryBP434 20 L)
      (fun _ p => p.val) J 1 m patterns f ≤ b650NativeFrameD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x f := by
    rw [hfactor]
    exact Nat.le_mul_of_pos_left _ hshared
  have hsubR : (parityFrameAuxD434 (SourceNativeMemoryBP434 20 L)
      (fun _ p => p.val) J 1 m patterns f : ℝ) ≤ (b650NativeFrameD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x f : ℝ) := by exact_mod_cast hsub
  exact hsubR.trans (b660_actual_parity_frame_D_window434
    L hL hS J m 0 (by norm_num) patterns x f)

/-- Source polynomial Z and k ranges plus the actual subexponential product
cap imply every numerical hypothesis needed by the harmonic envelope.
CZ and Ck are chosen before L; D, Z and the signed k are quantified later. -/
theorem parity_eventually_harmonic_scale_budget434
    (CZ Ck : ℝ) (hCZ : 0 ≤ CZ) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧
    ∀ Z : ℝ, Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
    ∀ D : ℕ, 0 < D → (D:ℝ) ≤ Real.exp (Real.sqrt L) →
    ∀ k : ℤ, |(k:ℝ)| ≤ L^Ck →
      1 ≤ Z*(D:ℝ) ∧
      |((2*k*(D:ℤ):ℤ):ℝ)| ≤ (Z*(D:ℝ))/128 ∧
      Real.log (⌈65*(Z*(D:ℝ))⌉₊:ℝ) ≤ 2*L := by
  filter_upwards [
    b638_eventually_log_power434 (4*CZ) 0 1 (by positivity) (by norm_num),
    b638_eventually_const_power434 4 (1/2) 1 (by norm_num),
    b638_eventually_poly_exp434 256 (CZ+Ck) 1 (by norm_num) (by norm_num),
    eventually_ge_atTop (4*Real.log 66),eventually_ge_atTop (1:ℝ)]
    with L hcz hsqrt hpoly h66 hL
  have hLp : 0 < L := by linarith
  simp only [Real.rpow_zero,mul_one,Real.rpow_one] at hcz hsqrt hpoly
  rw [← Real.sqrt_eq_rpow] at hsqrt
  refine ⟨hL,?_⟩
  intro Z hZlo hZhi D hD hDhi k hk
  have hZp : 0 < Z :=
    (mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hDp : 0 < (D:ℝ) := by exact_mod_cast hD
  have hD1 : 1 ≤ (D:ℝ) := by exact_mod_cast hD
  have hlogZlo : L-CZ*Real.log L ≤ Real.log Z := by
    have hh := Real.log_le_log
      (mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp (-CZ))) hZlo
    rw [Real.log_mul (Real.exp_pos L).ne'
      (Real.rpow_pos_of_pos hLp (-CZ)).ne',Real.log_exp,Real.log_rpow hLp] at hh
    linarith
  have hlogZhi : Real.log Z ≤ L+CZ*Real.log L := by
    have hh := Real.log_le_log hZp hZhi
    rw [Real.log_mul (Real.exp_pos L).ne'
      (Real.rpow_pos_of_pos hLp CZ).ne',Real.log_exp,Real.log_rpow hLp] at hh
    exact hh
  have hZ1 : 1 ≤ Z := by
    rw [←Real.exp_log hZp,←Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hX1 : 1 ≤ Z*(D:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hD1 hZp.le]
  have hXp : 0 < Z*(D:ℝ) := mul_pos hZp hDp
  have hpow : L^(CZ+Ck)*L^(-CZ)=L^Ck := by
    rw [←Real.rpow_add hLp]
    congr 1
    ring
  have h256 : 256*L^Ck ≤ Z := by
    calc
      _ = (256*L^(CZ+Ck))*L^(-CZ) := by rw [mul_assoc,hpow]
      _ ≤ Real.exp L*L^(-CZ) :=
        mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hLp.le _)
      _ ≤ Z := hZlo
  have hshift : |((2*k*(D:ℤ):ℤ):ℝ)| ≤ (Z*(D:ℝ))/128 := by
    have hk2 : |((2*k:ℤ):ℝ)| ≤ Z/128 := by
      push_cast
      rw [abs_mul]
      norm_num
      nlinarith
    calc
      _ = |((2*k:ℤ):ℝ)| * (D:ℝ) := by push_cast; rw [abs_mul,abs_of_pos hDp]
      _ ≤ (Z/128)*(D:ℝ) := mul_le_mul_of_nonneg_right hk2 hDp.le
      _ = _ := by ring
  have hcap : (⌈65*(Z*(D:ℝ))⌉₊:ℝ) ≤ 66*(Z*(D:ℝ)) := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 65*(Z*(D:ℝ)) by positivity)
    linarith
  have hcapP : 0 < (⌈65*(Z*(D:ℝ))⌉₊:ℝ) :=
    (by positivity : 0 < 65*(Z*(D:ℝ))).trans_le (Nat.le_ceil _)
  have hlogD : Real.log (D:ℝ) ≤ Real.sqrt L := by
    simpa only [Real.log_exp] using Real.log_le_log hDp hDhi
  refine ⟨hX1,hshift,?_⟩
  calc
    _ ≤ Real.log (66*(Z*(D:ℝ))) := Real.log_le_log hcapP hcap
    _ = Real.log 66+Real.log Z+Real.log (D:ℝ) := by
      rw [Real.log_mul (by norm_num : (66:ℝ)≠0) hXp.ne',
        Real.log_mul hZp.ne' hDp.ne']
      ring
    _ ≤ 2*L := by linarith

/-- Actual r20, ell=1 restoration-envelope bound for every original frame.
The repeated D_C, shift 2*k*D_C and harmonic scale Z*D_C are literal; all
scale hypotheses of the finite envelope are discharged uniformly. -/
theorem parity_eventually_actual_frame_harmonic_envelope434
    (J : ℕ) (CZ Ck : ℝ) (hCZ : 0 ≤ CZ) :
    ∀ᶠ L : ℝ in atTop, Real.exp 1 ≤ L ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (m : ℕ) (Nu : Type) [Fintype Nu]
      (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
      (x : MemoryIndependentState
        (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1)
      (f : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
        (SourceNativeMemoryBP434 20 L) J 1 m patterns)
      (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
    ∀ (k : ℤ), |(k:ℝ)| ≤ L^Ck →
    ∀ (K Cpsi : ℝ), 0 ≤ K →
    ∀ (psi : ℝ → ℂ),
      (∀ t, psi t ≠ 0 → t ∈ Set.Icc (1/64:ℝ) 64) →
      (∀ t, ‖psi t‖ ≤ K*L^Cpsi) →
    ∀ M : ℕ,
      let D := parityFrameAuxD434 (SourceNativeMemoryBP434 20 L)
        (fun _ p => p.val) J 1 m patterns f
      parityHarmonicDivisorEnvelope434 (Z*(D:ℝ)) (2*k*(D:ℤ)) psi M ≤
        (64*66*(3:ℝ)^15)*K*L^(15+Cpsi) := by
  filter_upwards [b651_eventually_parity_window_sqrt434 J 0 (by norm_num),
    parity_eventually_harmonic_scale_budget434 CZ Ck hCZ] with L hW hBudget
  refine ⟨hW.1,?_⟩
  intro hS m Nu inst patterns x f Z hZlo hZhi k hk K Cpsi hK psi hSupp hPsi M
  dsimp only
  let D := parityFrameAuxD434 (SourceNativeMemoryBP434 20 L)
    (fun _ p => p.val) J 1 m patterns f
  have hD : 0 < D := parity_frame_aux_D_pos434
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m patterns f
  have hDhi : (D:ℝ) ≤ Real.exp (Real.sqrt L) :=
    (parity_actual_frame_aux_window434 L hW.1 hS J m patterns x f).trans hW.2
  have hb := hBudget.2 Z hZlo hZhi D hD hDhi k hk
  exact parity_harmonic_cutoff_divisor_envelope434 L (Z*(D:ℝ)) K Cpsi
    hBudget.1 hb.1 hK (2*k*(D:ℤ)) hb.2.1 hb.2.2 psi hSupp hPsi M
end Green64Analytic.SourceBlockSieve

end

end

/-! ## FramePGate -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 24000

/-- The entire shared dilation of an actual physical frame is supported on
all original r20 P bands. Neither the distinguished SMALL group nor repeated
valuations at a stripped endpoint are removed. -/
theorem parity_actual_frame_shared_P_support434
    (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
    (positions : Finset ℤ) (x : B654ActualParityState434 L hS J positions)
    (f : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J 1 m patterns) :
    (parityFrameSharedD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x.val.2 f).primeFactors ⊆ sourceNativeOriginalG434 20 L := by
  have hd := parity_frame_shared_dvd_full_marks434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
    J 1 m patterns positions x f
  have hs := b657_actual_mark_product_support434 L hL hS J positions x
  intro p hp
  apply hs.2
  rcases Nat.mem_primeFactors.mp hp with ⟨hp,hpd,_⟩
  exact Nat.mem_primeFactors.mpr ⟨hp,hpd.trans hd,hs.1⟩

/-- The true shared factor is no larger than the complete native frame D,
which is bounded by the already proved original localization window. -/
theorem parity_actual_frame_shared_window434
    (L : ℝ) (hL : Real.exp 1 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
    (positions : Finset ℤ) (x : B654ActualParityState434 L hS J positions)
    (f : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J 1 m patterns) :
    (parityFrameSharedD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x.val.2 f : ℝ) ≤ (b651ParityWindowSize434 J 0 L : ℝ) := by
  have haux := parity_frame_aux_D_pos434
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m patterns f
  have hfactor := parity_frame_D_factor434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
    J 1 m patterns x.val.2 f
  have hsub : parityFrameSharedD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x.val.2 f ≤ b650NativeFrameD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x.val.2 f := by
    rw [hfactor]
    exact Nat.le_mul_of_pos_right _ haux
  have hsubR : (parityFrameSharedD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x.val.2 f : ℝ) ≤ (b650NativeFrameD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x.val.2 f : ℝ) := by exact_mod_cast hsub
  exact hsubR.trans (b660_actual_parity_frame_D_window434 L hL hS J m 0
    (by norm_num) patterns x.val.2 f)

/-- The actual r20 shared dilation fits the half-exponent of the Parity
sigma=1/44 P gate, uniformly over all full states, patterns and frames.
The size premise of B575 is discharged; J is fixed before L. -/
theorem parity_eventually_actual_frame_shared_half_Pcap434 (J : ℕ) :
    ∀ᶠ L : ℝ in atTop, Real.exp 1 ≤ L ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (m : ℕ) (Nu : Type) [Fintype Nu]
      (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
      (positions : Finset ℤ) (x : B654ActualParityState434 L hS J positions)
      (f : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
        (SourceNativeMemoryBP434 20 L) J 1 m patterns),
    (parityFrameSharedD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x.val.2 f : ℝ) ≤ Real.exp ((1/88:ℝ)*L) := by
  filter_upwards [b651_eventually_parity_window_sqrt434 J 0 (by norm_num),
    b638_eventually_const_power434 88 (1/2) 1 (by norm_num)] with L hW hRate
  refine ⟨hW.1,?_⟩
  intro hS m Nu inst patterns positions x f
  have hs : Real.sqrt L ≤ (1/88:ℝ)*L := by
    rw [Real.rpow_one] at hRate
    rw [Real.sqrt_eq_rpow]
    linarith
  exact (parity_actual_frame_shared_window434 L hW.1 hS J m patterns positions x f).trans
    (hW.2.trans (Real.exp_le_exp.mpr hs))

/-- Exact natural-factor identity at a positive physical endpoint; the
quotient is the literal signed quotient from the frame, not a fresh variable. -/
theorem parity_actual_positive_frame_quotient434
    (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
    (positions : Finset ℤ) (x : B654ActualParityState434 L hS J positions)
    (f : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J 1 m patterns) (hx : 0 < x.val.1.val) :
    let dR := parityFrameSharedD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x.val.2 f
    let w := x.val.1.val / (dR : ℤ)
    0 < w ∧ x.val.1.val.toNat = dR*w.toNat := by
  dsimp only
  let dR := parityFrameSharedD434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
    J 1 m patterns x.val.2 f
  have hdR : 0 < dR := parity_frame_shared_D_pos434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
    J 1 m patterns x.val.2 f
  have hdRz : (0:ℤ) < dR := by exact_mod_cast hdR
  have heq : x.val.1.val = (dR:ℤ)*(x.val.1.val/(dR:ℤ)) :=
    (Int.mul_ediv_cancel_of_dvd
      (parity_actual_frame_shared_divides434 L hL hS J m patterns positions x f)).symm
  have hw : 0 < x.val.1.val/(dR:ℤ) := by
    have hh : 0 < (dR:ℤ)*(x.val.1.val/(dR:ℤ)) := by rw [←heq]; exact hx
    exact (mul_pos_iff_of_pos_left hdRz).mp hh
  refine ⟨hw,?_⟩
  have hcast : (x.val.1.val.toNat:ℤ) =
      (dR:ℤ)*((x.val.1.val/(dR:ℤ)).toNat:ℤ) := by
    simpa only [Int.toNat_of_nonneg hx.le,Int.toNat_of_nonneg hw.le] using heq
  exact_mod_cast hcast

/-- B575 multiplicativity is applied to the complete actual shared product.
The original P gate changes with D_R and is never declared invariant. -/
theorem parity_actual_frame_Ppart_identity434
    (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
    (positions : Finset ℤ) (x : B654ActualParityState434 L hS J positions)
    (f : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J 1 m patterns) (hx : 0 < x.val.1.val) :
    let dR := parityFrameSharedD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x.val.2 f
    sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) x.val.1.val.toNat =
      dR*sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L)
        (x.val.1.val/(dR:ℤ)).toNat := by
  dsimp only
  have hq := parity_actual_positive_frame_quotient434 L hL hS J m patterns positions x f hx
  dsimp only at hq
  rw [hq.2]
  exact b575_shared_dilation_Ppart _ _ _
    (parity_frame_shared_D_pos434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x.val.2 f)
    (by omega)
    (parity_actual_frame_shared_P_support434 L hL hS J m patterns positions x f)

/-- Failure of either ORIGINAL physical P cap in an allowed actual frame
forces the corresponding genuine half-threshold stripped P-part tail.
Both endpoints use the SAME full shared dilation; all size/support premises
of B575 are proved for the actual r20 family. -/
theorem parity_eventually_actual_frame_failed_Pgates434 (J : ℕ) :
    ∀ᶠ L : ℝ in atTop, Real.exp 1 ≤ L ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (m : ℕ) (Nu : Type) [Fintype Nu]
      (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
      (positions : Finset ℤ) (k : ℤ) (x y : B654ActualParityState434 L hS J positions)
      (f : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
        (SourceNativeMemoryBP434 20 L) J 1 m patterns)
      (hx : 0 < x.val.1.val) (hy : 0 < y.val.1.val)
      (hallowed : b650IntegerFrameAllowed434
        (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
        J 1 m patterns positions 1 (2*k) x y f),
    let dR := parityFrameSharedD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m patterns x.val.2 f
    let P := sourceNativeOriginalG434 20 L
    (⌊Real.exp ((1/44:ℝ)*L)⌋₊ < sourceOriginalPPrimePart P x.val.1.val.toNat ∨
      ⌊Real.exp ((1/44:ℝ)*L)⌋₊ < sourceOriginalPPrimePart P y.val.1.val.toNat) →
    (⌊Real.exp ((1/88:ℝ)*L)⌋₊ < sourceOriginalPPrimePart P (x.val.1.val/(dR:ℤ)).toNat ∨
      ⌊Real.exp ((1/88:ℝ)*L)⌋₊ < sourceOriginalPPrimePart P (y.val.1.val/(dR:ℤ)).toNat) := by
  filter_upwards [parity_eventually_actual_frame_shared_half_Pcap434 J] with L hL
  refine ⟨hL.1,?_⟩
  intro hS m Nu inst patterns positions k x y f hx hy hallowed
  dsimp only
  have hLg : 1 < L := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hL.1
  let dR := parityFrameSharedD434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
    J 1 m patterns x.val.2 f
  have hdR : 0 < dR := parity_frame_shared_D_pos434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
    J 1 m patterns x.val.2 f
  have hdRz : (0:ℤ) < dR := by exact_mod_cast hdR
  have hsup := parity_actual_frame_shared_P_support434 L hLg hS J m patterns positions x f
  have hsmall : (dR:ℝ) ≤ Real.exp (((1/44:ℝ)/2)*L) := by
    convert hL.2 hS m Nu patterns positions x f using 1 <;> norm_num
  have hqx := parity_actual_positive_frame_quotient434 L hLg hS J m patterns positions x f hx
  dsimp only at hqx
  have hqy := (parity_actual_allowed_frame_quotients434
    L hLg hS J m patterns positions k x y f hallowed).2.1
  have hwpy : 0 < y.val.1.val/(dR:ℤ) := by
    have hh : 0 < (dR:ℤ)*(y.val.1.val/(dR:ℤ)) := by rw [←hqy]; exact hy
    exact (mul_pos_iff_of_pos_left hdRz).mp hh
  have hny : y.val.1.val.toNat=dR*(y.val.1.val/(dR:ℤ)).toNat := by
    have hcast : (y.val.1.val.toNat:ℤ) =
        (dR:ℤ)*((y.val.1.val/(dR:ℤ)).toNat:ℤ) := by
      simpa only [Int.toNat_of_nonneg hy.le,Int.toNat_of_nonneg hwpy.le] using hqy
    exact_mod_cast hcast
  intro hfail
  rcases hfail with hf | hf
  · left
    rw [hqx.2] at hf
    have ht := b575_failed_physical_Pcap_has_stripped_tail
      (sourceNativeOriginalG434 20 L) dR _ (1/44) L hdR
      (by omega) hsup hsmall hf
    norm_num at ht ⊢
    exact ht
  · right
    rw [hny] at hf
    have ht := b575_failed_physical_Pcap_has_stripped_tail
      (sourceNativeOriginalG434 20 L) dR _ (1/44) L hdR
      (by omega) hsup hsmall hf
    norm_num at ht ⊢
    exact ht
end Green64Analytic.SourceBlockSieve

end

end

