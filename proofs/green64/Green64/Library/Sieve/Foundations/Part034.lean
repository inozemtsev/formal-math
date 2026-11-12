module

public import Green64.Library.Sieve.Foundations.Part033
public import Green64.Library.Sieve.Foundations.Part024
public import Green64.Library.Sieve.Foundations.Part007
public import Green64.Library.Sieve.Foundations.Part031
public import Green64.Library.Weights.Part005

@[expose] public section

/-!
# Sieve / Foundations / Part034

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalHistoricalLowfreqActualB633CharacterProjector -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2700000

/-- LITERAL original Parity(4.16) B633 two-core prime-slot atom,
with the original reserved Q/B509 residual, rough cofactor powers,
W1 and signed epsilon, but WITHOUT the two cofactor alpha and
Dirichlet character factors. The atom has no new arithmetic mask. -/
def parityOriginalHistoricalB633CharacterFreeAtom434
    (L rho xi1 xi2 xi3 : ℝ) (signed : Bool)
    (residual : ℕ → ℂ) (lo hi m mp z zp : ℕ) : ℂ :=
  let P := sourceOriginalPAllActualBands 20 L
  let Pall := Finset.univ.biUnion P
  imaginaryPower m xi1 * imaginaryPower mp xi2 *
    imaginaryPower z xi3 *
    imaginaryPower (z/mp) rho * imaginaryPower (zp/m) (-rho) *
    b633PrimeRest434 lo hi 0 residual (sourceOriginalOrdinaryPart Pall (z/mp)) *
    star (b633PrimeRest434 lo hi 0 residual (sourceOriginalOrdinaryPart Pall (zp/m))) *
    (((sourceMarkedWeight (1/2:ℝ) 1 P (z/mp) *
        sourceMarkedWeight (1/2:ℝ) 1 P (zp/m) : ℝ):ℂ)) *
    (((groupSign P signed (z/mp) * groupSign P signed (zp/m) : ℝ):ℂ))

/-- Exact factorization of the ACTUAL original first and second
B633 prime-slot summand, before ANY χ cancellation or Fourier
truncation; no condition that the fine alpha or H0 is nonzero. -/
theorem parity_original_historical_B633_full_character_factor434
    (L rho xi1 xi2 xi3 : ℝ) (signed : Bool)
    (alpha residual : ℕ → ℂ) (q : ℕ)
    (chi : DirichletCharacter ℂ q)
    (lo hi m mp z zp : ℕ) :
    parityOriginalHistoricalB633PhysicalPairTerm434
      L rho xi1 xi2 xi3 signed alpha residual q chi lo hi m mp z zp =
    (parityOriginalHistoricalB633CharacterFreeAtom434
      L rho xi1 xi2 xi3 signed residual lo hi m mp z zp *
        alpha m * star (alpha mp)) *
        chi (mp : ZMod q) * star (chi (m : ZMod q)) := by
  unfold parityOriginalHistoricalB633PhysicalPairTerm434
    parityOriginalHistoricalB633CharacterFreeAtom434
  ring

/-- True original SOURCE `sourceNativePrimeCore` reserved Q interval
and skipped-prime residual do not depend on the character χ.
Character dependence is confined to its separate first/second
cofactor core phases. This is definitional, not a distributional
assumption or cancellation claim. -/
theorem parity_original_historical_B633_reserved_source_chi_invariant434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ) (q : ℕ)
    (chi chi0 : DirichletCharacter ℂ q) :
    (sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0).residual =
      (sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi0 0 0).residual ∧
    (sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0).lo =
      (sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi0 0 0).lo ∧
    (sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0).hi =
      (sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi0 0 0).hi := by
  exact ⟨rfl,rfl,rfl⟩

/-- SOURCE-FAITHFUL character projection OF THE ACTUAL ORIGINAL
B633 FIRST/SECOND PRIME-SLOT CORES, with genuine b629 fine alpha,
Q-reserved B509 residual, both H0 prime slots, W1, both signs and
all five imaginary powers. The whole χ sum is taken BEFORE imposing
integer odd e=(m'-m)/k. No χ-individual ghost vanishing is claimed.

The unrestricted finite m,m',z,z' family is arbitrary, including
zero-fine-alpha terms; the identity holds termwise at the COMPLETE
χ-sum level, not after applying norm to a signed subset. This
closes the missing literal B633 χ-dependent cofactor extraction,
but NOT the entire source n/e/z reindex or Parity4.17 saving. -/
theorem parity_eventually_original_unrestricted_actual_B633_full_chi_projector434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (rho xi1 xi2 xi3 : ℝ) (signed : Bool)
        {ι : Type} [DecidableEq ι] (s : Finset ι)
        (m mp z zp : ι → ℕ),
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let A : ι → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
        L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
        (m i) (mp i) (z i) (zp i)
      (∑i∈s, (A i*alpha (m i)*star (alpha (mp i))) *
        (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
          then (1:ℂ) else 0)) =
      ∑chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi *
        (∑i∈s,
          let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
            (2*k.natAbs) chi 0 0
          parityOriginalHistoricalB633PhysicalPairTerm434
            L rho xi1 xi2 xi3 signed alpha F.residual
            (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)) := by
  filter_upwards [parity_eventually_original_full_unrestricted_actual_alpha_odd_e_projector434
    S beta gamma Ck hS hbeta hgamma] with L hProj
  refine ⟨hProj.1,?_⟩
  intro prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 signed ι decι s m mp z zp
  dsimp only
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let A : ι → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    (m i) (mp i) (z i) (zp i)
  have hMask := hProj.2 prime l u hl hlow K k hk hkBound s m mp A
  dsimp only at hMask
  calc
    _ = ∑chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
        (∑i∈s, (A i*alpha (m i)*star (alpha (mp i))) *
          chi (mp i:ZMod (2*k.natAbs)) *
          star (chi (m i:ZMod (2*k.natAbs)))) := hMask
    _ = _ := by
      apply Finset.sum_congr rfl
      intro chi hchi
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) chi 0 0
      have hInv := parity_original_historical_B633_reserved_source_chi_invariant434
        d L band slot δ ξ K alpha (2*k.natAbs) chi 1
      have hChar := parity_original_historical_B633_full_character_factor434
        L rho xi1 xi2 xi3 signed alpha F.residual
        (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)
      change (A i*alpha (m i)*star (alpha (mp i))) *
        chi (mp i:ZMod (2*k.natAbs)) *
        star (chi (m i:ZMod (2*k.natAbs))) =
        parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha F.residual
          (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)
      rw [hChar]
      dsimp only [A]
      rw [hInv.1,hInv.2.1,hInv.2.2]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqActualB633ProjectedBall -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- EXACT original Parity (4.16) actual fine-alpha, B509 skipped-Q
residual, W1 and signed epsilon complete χ projector AT the genuine
LOW-frequency three-dimensional Fourier BALL, for ALL positive and
zero unrestricted B633 cofactor terms and any real Schwartz source.

The FULL χ sum is formed before imposing integer odd e and before
the Fourier-ball truncation. In particular there is no false claim
that each χ-component separately vanishes for fractional e or
that one may take norms of a signed subset. This is an exact
original-coefficient source equality and not a spectral saving or a
complete physical n/e/z source-to-(4.17) reindex. -/
theorem parity_eventually_original_unrestricted_actual_B633_projected_fourier_ball434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (rho xi1 xi2 xi3 : ℝ) (signed : Bool)
        {ι : Type} [DecidableEq ι] (s : Finset ι)
        (m mp z zp : ι → ℕ)
        (t : ι → EuclideanSpace ℝ (Fin 3))
        (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) (R : ℝ),
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let A : ι → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
        L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
        (m i) (mp i) (z i) (zp i)
      let Wodd : ι → ℂ := fun i => A i*alpha (m i)*star (alpha (mp i))*
        (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
          then (1:ℂ) else 0)
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤R}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434 s Wodd t f ζ) =
      ∑chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi *
        (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤R}:Set _),
          parityOriginal3DPhysicalFiniteTwistedSource434 s
            (fun i =>
              let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
                (2*k.natAbs) chi 0 0
              parityOriginalHistoricalB633PhysicalPairTerm434
                L rho xi1 xi2 xi3 signed alpha F.residual
                (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i))
            t f ζ) := by
  filter_upwards [parity_eventually_original_actual_alpha_odd_e_projected_fourier_ball434
    S beta gamma Ck hS hbeta hgamma] with L hProj
  refine ⟨hProj.1,?_⟩
  intro prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 signed ι decι s m mp z zp t f R
  dsimp only
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let A : ι → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    (m i) (mp i) (z i) (zp i)
  let Wodd : ι → ℂ := fun i => A i*alpha (m i)*star (alpha (mp i))*
    (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
      then (1:ℂ) else 0)
  have hBall := hProj.2 prime l u hl hlow K k hk hkBound
    s m mp A t f R
  dsimp only at hBall
  change (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤R}:Set _),
    parityOriginal3DPhysicalFiniteTwistedSource434 s Wodd t f ζ) = _
  rw [hBall]
  apply Finset.sum_congr rfl
  intro chi hchi
  congr 1
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) chi 0 0
  have hInv := parity_original_historical_B633_reserved_source_chi_invariant434
    d L band slot δ ξ K alpha (2*k.natAbs) chi 1
  have hW : (fun i : ι => (A i*alpha (m i)*star (alpha (mp i))) *
      chi (mp i:ZMod (2*k.natAbs)) *
      star (chi (m i:ZMod (2*k.natAbs)))) =
      (fun i : ι => parityOriginalHistoricalB633PhysicalPairTerm434
        L rho xi1 xi2 xi3 signed alpha F.residual
        (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)) := by
    funext i
    have hChar := parity_original_historical_B633_full_character_factor434
      L rho xi1 xi2 xi3 signed alpha F.residual
      (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)
    rw [hChar]
    dsimp only [A]
    rw [hInv.1,hInv.2.1,hInv.2.2]
  rw [hW]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqB633PointwiseChiSource -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2300000

/-- Literal original B633, single cofactor pair, arbitrary m,m',z,z' (including
zero coefficients): the *entire* Parity(2.6) character projection equals the
correct odd-integer e detector. No SOURCE n/e artificial cutoff is inserted. -/
theorem parity_eventually_original_actual_B633_pointwise_full_chi434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (rho xi1 xi2 xi3 : ℝ) (signed : Bool) (m mp z zp : ℕ),
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let A := parityOriginalHistoricalB633CharacterFreeAtom434
        L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi m mp z zp
      (A*alpha m*star (alpha mp)) *
        (if k∣(mp:ℤ)-(m:ℤ) ∧ Odd (((mp:ℤ)-(m:ℤ))/k)
         then (1:ℂ) else 0) =
        ∑chi : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs chi *
            (let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
              (2*k.natAbs) chi 0 0
             parityOriginalHistoricalB633PhysicalPairTerm434
              L rho xi1 xi2 xi3 signed alpha F.residual
              (2*k.natAbs) chi F.lo F.hi m mp z zp) := by
  filter_upwards [parity_eventually_original_unrestricted_actual_B633_full_chi_projector434
    S beta gamma Ck hS hbeta hgamma] with L hProj
  refine ⟨hProj.1,?_⟩
  intro prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 signed m mp z zp
  dsimp only
  have h := hProj.2 prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 signed ({()} : Finset Unit)
    (fun _ => m) (fun _ => mp) (fun _ => z) (fun _ => zp)
  simpa only [Finset.sum_singleton] using h
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqFullyProjectedActualGhost -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2300000

/-- For the actual B633 ORIGINAL cofactor/ordinary-divisor carrier, the
COMPLETE Parity character projector has no off-physical weighted ghosts.
This includes EVERY noninteger/even/negative reconstructed e and zero
fine-alpha or prime-slot term. Crucially nothing is assumed about the
individual characters vanishing when e is not an odd integer. The
only index conditions are the genuine positive endpoints, original
rough-cofactor dyad, ordinary-P divisor constraints and shift z'=z+2k.
This is a source-weighted equality, not a false signed-subsum inequality. -/
theorem parity_eventually_original_full_chi_B633_ghost_weighted_zero434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L) (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (rho xi1 xi2 xi3 U E V Z : ℝ) (signed : Bool),
      0 < U → 0 < E → 0 < V → 0 < Z →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
      ∀ (m mp z zp : ℕ)
        (hm : 0 < m) (hmp : 0 < mp) (hz : 0 < z) (hzp : 0 < zp)
        (hmK : m∈K) (hmpK : mp∈K) (hNe : m≠mp)
        (hShift : (z:ℤ)+2*k=(zp:ℤ))
        (hDivMp : mp∣sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) z)
        (hDivM : m∣sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) zp),
      ∀ (buf : ℝ → ℂ) (a b : ℝ),
      (hSmooth : ContDiff ℝ ∞ buf) →
      (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b) →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let A := parityOriginalHistoricalB633CharacterFreeAtom434
        L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi m mp z zp
      let Wproj := (A*alpha m*star (alpha mp)) *
        (if k∣(mp:ℤ)-(m:ℤ) ∧ Odd (((mp:ℤ)-(m:ℤ))/k)
         then (1:ℂ) else 0)
      (hGhost : ¬(∃ en : ℕ, Odd en ∧ 0 < en ∧
        ∃ n : ℕ,
          n∈parityOriginalHistoricalFullNEnvelope434 V ∧
          (mp,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
            d L band slot δ (Nat.ceil (6*U*V)) en m K
            (parityOriginalHistoricalFullNEnvelope434 V) k
            (parityOriginalHistoricalActualZDyadicScale434 z) ∧
          parityOriginalHistoricalCanonicalZ434 en m mp n=z)) →
      Wproj * parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hLw U E V Z k buf a b hSmooth hBufSupport
        (parityOriginalHistoricalRealLogTriple434 U Z m mp z) = 0 := by
  filter_upwards [parity_eventually_original_actual_B633_pointwise_full_chi434
      S beta gamma Ck hS hbeta hgamma,
    parity_eventually_original_projected_actual_B633_weighted_ghost_zero434
      S beta gamma Ck hS hbeta hgamma] with L hProj hGhostL
  refine ⟨hGhostL.1,?_⟩
  intro hLw prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ hDyad
    m mp z zp hm hmp hz hzp hmK hmpK hNe hShift hDivMp hDivM
    buf a b hSmooth hBufSupport
  dsimp only
  intro hGhost
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let A := parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi m mp z zp
  let Wproj := (A*alpha m*star (alpha mp)) *
    (if k∣(mp:ℤ)-(m:ℤ) ∧ Odd (((mp:ℤ)-(m:ℤ))/k)
     then (1:ℂ) else 0)
  let f : ℂ := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf a b hSmooth hBufSupport
    (parityOriginalHistoricalRealLogTriple434 U Z m mp z)
  change Wproj * f = 0
  by_cases hMask : k∣(mp:ℤ)-(m:ℤ) ∧ Odd (((mp:ℤ)-(m:ℤ))/k)
  · let eInt : ℤ := ((mp:ℤ)-(m:ℤ))/k
    have hDet : (mp:ℤ)-(m:ℤ)=eInt*k := by
      exact (Int.ediv_mul_cancel hMask.1).symm
    have hPoint := hProj.2 prime l u hl hlow K k hk hkBound
      d band slot δ ξ rho xi1 xi2 xi3 signed m mp z zp
    change Wproj = ∑chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
        (let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0
         parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha F.residual
          (2*k.natAbs) chi F.lo F.hi m mp z zp) at hPoint
    rw [hPoint,Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro chi hchi
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
      (2*k.natAbs) chi 0 0
    have hZero := hGhostL.2 hLw prime l u hl hlow K k hk hkBound
      d band slot δ ξ chi rho xi1 xi2 xi3 U E V Z signed m mp z zp
      eInt hU hE hV hZ hm hmp hz hzp hDyad hNe hDet hMask.2
      hShift hDivMp hDivM buf a b hSmooth hBufSupport hGhost
    change parityOriginalHistoricalB633PhysicalPairTerm434
      L rho xi1 xi2 xi3 signed alpha F.residual
      (2*k.natAbs) chi F.lo F.hi m mp z zp * f = 0 at hZero
    calc
      _ = parityShiftTwoMaskCoefficient434 k.natAbs chi *
        (parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha F.residual
          (2*k.natAbs) chi F.lo F.hi m mp z zp * f) := by ring
      _ = 0 := by rw [hZero]; ring
  · have hW : Wproj=0 := by
      dsimp [Wproj]
      simp [hMask]
    simp [hW]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqFullChiBallTransfer -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- SOURCE-EXACT fixed-(k,Z) COMPLETE-CHARACTER signed B633 Fourier-ball
inequality on the original unrestricted positive/divisor cofactor carrier.
All complex terms carry the native b629 alpha, original H0/B509 prime
residual, W1, epsilon and 3D Schwartz eta_e eta_n with true h=-2.

The left hand side is the full Parity(2.6) projected cofactor sum on the
ACTUAL physical capfree (e,n) carrier; it is bounded by the absolute
value of the COMPLETE chi-projected UNRESTRICTED signed B633 Fourier
ball PLUS an actual positive weighted ghost coefficient mass times
the genuine Schwartz H-moment divided by T^H. No per-character ghost
vanishing, no signed-subset monotonicity, no #chi/#Z/#e hidden factor.
The full ORIGINAL B-prime source-to-(m,m',z) fibre reindex, and the
unrestricted Parity(4.17) saving itself, are separate obligations. -/
theorem parity_eventually_original_full_chi_actual_B633_ball_le_signed_correlator434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L) (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (rho xi1 xi2 xi3 U E V Z : ℝ) (signed : Bool),
      0<U → 0<E → 0<V → 0<Z →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
      ∀ {ι : Type} [DecidableEq ι] (s : Finset ι)
        (m mp z zp : ι → ℕ),
      (∀ i∈s, 0 < m i ∧ 0 < mp i ∧ 0 < z i ∧ 0 < zp i ∧
        m i ∈ K ∧ mp i ∈ K ∧ m i ≠ mp i ∧
        (z i:ℤ)+2*k=(zp i:ℤ) ∧
        mp i∣sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (z i) ∧
        m i∣sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (zp i)) →
      ∀ (buf : ℝ → ℂ) (a b : ℝ)
        (hSmooth : ContDiff ℝ ∞ buf)
        (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
        (H : ℕ) (T : ℝ), 0<T →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let A : ι → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
        L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
        (m i) (mp i) (z i) (zp i)
      let Wproj : ι → ℂ := fun i => A i*alpha (m i)*star (alpha (mp i))*
        (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
         then (1:ℂ) else 0)
      let Wchi : DirichletCharacter ℂ (2*k.natAbs) → ι → ℂ := fun chi i =>
        let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0
        parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha F.residual
          (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)
      let physical : ι → Prop := fun i =>
        ∃ en : ℕ, Odd en ∧ 0 < en ∧
          ∃ n : ℕ,
            n∈parityOriginalHistoricalFullNEnvelope434 V ∧
            (mp i,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
              d L band slot δ (Nat.ceil (6*U*V)) en (m i) K
              (parityOriginalHistoricalFullNEnvelope434 V) k
              (parityOriginalHistoricalActualZDyadicScale434 (z i)) ∧
            parityOriginalHistoricalCanonicalZ434 en (m i) (mp i) n=z i
      let t : ι → EuclideanSpace ℝ (Fin 3) := fun i =>
        parityOriginalHistoricalRealLogTriple434 U Z (m i) (mp i) (z i)
      let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hLw U E V Z k buf a b hSmooth hBufSupport
      ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
          parityOriginal3DPhysicalFiniteTwistedSource434
            (s.filter physical) Wproj t f ζ‖ ≤
      ‖∑chi : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs chi *
            (∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
              parityOriginal3DPhysicalFiniteTwistedSource434
                s (Wchi chi) t f ζ)‖ +
      parityOriginal3DPhysicalFiniteCoefficientMass434
        (s.filter (fun i => ¬physical i)) Wproj *
        (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) := by
  filter_upwards [parity_eventually_original_full_chi_B633_ghost_weighted_zero434
      S beta gamma Ck hS hbeta hgamma,
    parity_eventually_original_unrestricted_actual_B633_projected_fourier_ball434
      S beta gamma Ck hS hbeta hgamma] with L hGhostL hProjL
  refine ⟨hGhostL.1,?_⟩
  intro hLw prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ hDyad
    ι decι s m mp z zp hCarrier buf a b hSmooth hBufSupport H T hT
  dsimp only
  classical
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let A : ι → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    (m i) (mp i) (z i) (zp i)
  let Wproj : ι → ℂ := fun i => A i*alpha (m i)*star (alpha (mp i))*
    (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
     then (1:ℂ) else 0)
  let Wchi : DirichletCharacter ℂ (2*k.natAbs) → ι → ℂ := fun chi i =>
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
      (2*k.natAbs) chi 0 0
    parityOriginalHistoricalB633PhysicalPairTerm434
      L rho xi1 xi2 xi3 signed alpha F.residual
      (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)
  let physical : ι → Prop := fun i =>
    ∃ en : ℕ, Odd en ∧ 0 < en ∧ ∃ n : ℕ,
      n∈parityOriginalHistoricalFullNEnvelope434 V ∧
      (mp i,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ (Nat.ceil (6*U*V)) en (m i) K
        (parityOriginalHistoricalFullNEnvelope434 V) k
        (parityOriginalHistoricalActualZDyadicScale434 (z i)) ∧
      parityOriginalHistoricalCanonicalZ434 en (m i) (mp i) n=z i
  let t : ι → EuclideanSpace ℝ (Fin 3) := fun i =>
    parityOriginalHistoricalRealLogTriple434 U Z (m i) (mp i) (z i)
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf a b hSmooth hBufSupport
  have hWeighted : ∀i∈s, ¬physical i → Wproj i*f (t i)=0 := by
    intro i hi hnot
    rcases hCarrier i hi with ⟨hm,hmp,hz,hzp,hmK,hmpK,hNe,hShift,hDivMp,hDivM⟩
    exact hGhostL.2 hLw prime l u hl hlow K k hk hkBound
      d band slot δ ξ rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ hDyad
      (m i) (mp i) (z i) (zp i) hm hmp hz hzp hmK hmpK hNe
      hShift hDivMp hDivM buf a b hSmooth hBufSupport hnot
  have hTransfer := parity_original_historical_weighted_3d_source_ball_le_full_plus_ghost434
    s physical Wproj t H L hLw U E V Z k buf a b hSmooth hBufSupport
    T hT hWeighted
  have hProject := hProjL.2 prime l u hl hlow K k hk hkBound
    d band slot δ ξ rho xi1 xi2 xi3 signed s m mp z zp t f T
  change (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434 s Wproj t f ζ) =
    ∑chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434 s (Wchi chi) t f ζ) at hProject
  rw [hProject] at hTransfer
  exact hTransfer
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqProjectorCarrierFilter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2100000

/-- The COMPLETE original odd-integer-e Parity(2.6) projector and
actual K-restricted fine coefficient make all out-of-K and diagonal
m=m' cofactor terms EXACTLY ZERO. In particular, an m=m' term
cannot survive the whole character sum when k != 0; no complex
subsum is discarded by a triangle inequality. -/
theorem parity_original_actual_odd_projector_bad_cofactor_zero434
    (K : Finset ℕ) (a : ℕ → ℂ) (k : ℤ)
    (m mp : ℕ) (A : ℂ)
    (hbad : ¬(m∈K ∧ mp∈K ∧ m≠mp)) :
    (A*restrictSequence K a m*star (restrictSequence K a mp)) *
      (if k∣(mp:ℤ)-(m:ℤ) ∧ Odd (((mp:ℤ)-(m:ℤ))/k)
       then (1:ℂ) else 0)=0 := by
  classical
  by_cases hm : m∈K
  · by_cases hmp : mp∈K
    · have heq : m=mp := by
        by_contra hn
        exact hbad ⟨hm,hmp,hn⟩
      subst mp
      simp
    · simp [restrictSequence,hmp]
  · simp [restrictSequence,hm]

/-- Exact finite ORIGINAL 3D Fourier-BALL integral over all unrestricted
cofactor labels equals the same integral restricted to m,m' in the
true fine-alpha K support and m != m'. This holds because the WHOLE
projector annihilates the discarded coefficients pointwise, not
because complex-valued correlation subsums have monotone norms. -/
theorem parity_original_actual_odd_projector_ball_carrier_filter434
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (K : Finset ℕ) (a : ℕ → ℂ) (k : ℤ)
    (m mp : ι → ℕ) (A : ι → ℂ)
    (t : ι → EuclideanSpace ℝ (Fin 3))
    (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) (T : ℝ) :
    let good : ι → Prop := fun i => m i∈K ∧ mp i∈K ∧ m i≠mp i
    let W : ι → ℂ := fun i =>
      (A i*restrictSequence K a (m i)*star (restrictSequence K a (mp i))) *
      (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
       then (1:ℂ) else 0)
    (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434 s W t f ζ) =
    (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434 (s.filter good) W t f ζ) := by
  classical
  dsimp only
  let good : ι → Prop := fun i => m i∈K ∧ mp i∈K ∧ m i≠mp i
  let W : ι → ℂ := fun i =>
    (A i*restrictSequence K a (m i)*star (restrictSequence K a (mp i))) *
    (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
     then (1:ℂ) else 0)
  have hzero (i : ι) (hi : ¬good i) : W i=0 :=
    parity_original_actual_odd_projector_bad_cofactor_zero434
      K a k (m i) (mp i) (A i) hi
  rw [parity_original_3d_physical_source_finite_fourier_ball_fubini434
        s W t f T,
      parity_original_3d_physical_source_finite_fourier_ball_fubini434
        (s.filter good) W t f T]
  symm
  apply Finset.sum_subset (Finset.filter_subset good s)
  intro i hi hnot
  have hb : ¬good i := by
    intro hg
    exact hnot (Finset.mem_filter.mpr ⟨hi,hg⟩)
  simp [hzero i hb]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqFullCharacterIndexFilter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2500000

/-- For actual Parity4.16 original B633 cores, the ENTIRE chi-summed
3D Fourier ball on an unrestricted finite cofactor family is EXACTLY
equal to the ball with both fine-alpha K-support gates and m!=m'
inserted. This is NOT a per-character equality: off-diagonal
selection is implemented by character orthogonality BEFORE any norm.
There is no prime-slot/physical n support gate. -/
theorem parity_eventually_original_unrestricted_actual_B633_full_chi_carrier_filter434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (rho xi1 xi2 xi3 : ℝ) (signed : Bool)
        {ι : Type} [DecidableEq ι] (s : Finset ι)
        (m mp z zp : ι → ℕ)
        (t : ι → EuclideanSpace ℝ (Fin 3))
        (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) (T : ℝ),
      let good : ι → Prop := fun i => m i∈K ∧ mp i∈K ∧ m i≠mp i
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let A : ι → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
        L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
        (m i) (mp i) (z i) (zp i)
      let Wchi : DirichletCharacter ℂ (2*k.natAbs) → ι → ℂ := fun chi i =>
        let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0
        parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha F.residual
          (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)
      (∑chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi *
          (∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
            parityOriginal3DPhysicalFiniteTwistedSource434 s (Wchi chi) t f ζ)) =
      (∑chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi *
          (∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
            parityOriginal3DPhysicalFiniteTwistedSource434
              (s.filter good) (Wchi chi) t f ζ)) := by
  filter_upwards [parity_eventually_original_unrestricted_actual_B633_projected_fourier_ball434
    S beta gamma Ck hS hbeta hgamma] with L hProj
  refine ⟨hProj.1,?_⟩
  intro prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 signed ι decι s m mp z zp t f T
  dsimp only
  let good : ι → Prop := fun i => m i∈K ∧ mp i∈K ∧ m i≠mp i
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let A : ι → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    (m i) (mp i) (z i) (zp i)
  let Wchi : DirichletCharacter ℂ (2*k.natAbs) → ι → ℂ := fun chi i =>
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
      (2*k.natAbs) chi 0 0
    parityOriginalHistoricalB633PhysicalPairTerm434
      L rho xi1 xi2 xi3 signed alpha F.residual
      (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)
  let Wproj : ι → ℂ := fun i => A i*alpha (m i)*star (alpha (mp i))*
    (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
     then (1:ℂ) else 0)
  have hFull := hProj.2 prime l u hl hlow K k hk hkBound
    d band slot δ ξ rho xi1 xi2 xi3 signed s m mp z zp t f T
  have hRestr := hProj.2 prime l u hl hlow K k hk hkBound
    d band slot δ ξ rho xi1 xi2 xi3 signed (s.filter good)
    m mp z zp t f T
  have hFilter := parity_original_actual_odd_projector_ball_carrier_filter434
    s K (b629ActualFineAlpha434 prime L S gamma l u) k m mp A t f T
  change (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434 s Wproj t f ζ) =
    (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434 (s.filter good) Wproj t f ζ)
    at hFilter
  change (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434 s Wproj t f ζ) =
    ∑chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434 s (Wchi chi) t f ζ)
    at hFull
  change (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434 (s.filter good) Wproj t f ζ) =
    ∑chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434
          (s.filter good) (Wchi chi) t f ζ)
    at hRestr
  exact hFull.symm.trans (hFilter.trans hRestr)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqUnrestrictedFullChiBall -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- Stronger fixed-(k,Z) original B633 SOURCE-Fourier inequality over ALL
unrestricted cofactor labels, without manually assuming m,m' are in
K or m != m'. The complete chi projector cancels those terms only
AFTER summation over characters. Original positive z,z+2k, both
ordinary-P divisor index gates and source dyads remain literal.

The exact physical-index Fourier ball is controlled by the norm of
the COMPLETE unrestricted character-averaged Parity4.17 B633 signed
Fourier ball plus the ACTUAL nonphysical coefficient mass times the
source 3D Schwartz H-moment/T^H, with no character count loss.
The remaining SOURCE e,n,z reindex and final Eq4.17 analytic bound
are *not* assumed or claimed by this local theorem. -/
theorem parity_eventually_original_unrestricted_actual_B633_ball_le_full_chi_correlator434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L) (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (rho xi1 xi2 xi3 U E V Z : ℝ) (signed : Bool),
      0<U → 0<E → 0<V → 0<Z →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
      ∀ {ι : Type} [DecidableEq ι] (s : Finset ι)
        (m mp z zp : ι → ℕ),
      (∀ i∈s, 0 < m i ∧ 0 < mp i ∧ 0 < z i ∧ 0 < zp i ∧
          (z i:ℤ)+2*k=(zp i:ℤ) ∧
        mp i∣sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (z i) ∧
        m i∣sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (zp i)) →
      ∀ (buf : ℝ → ℂ) (a b : ℝ)
        (hSmooth : ContDiff ℝ ∞ buf)
        (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
        (H : ℕ) (T : ℝ), 0<T →
      let good : ι → Prop := fun i => m i∈K ∧ mp i∈K ∧ m i≠mp i
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let A : ι → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
        L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
        (m i) (mp i) (z i) (zp i)
      let Wproj : ι → ℂ := fun i => A i*alpha (m i)*star (alpha (mp i))*
        (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
         then (1:ℂ) else 0)
      let Wchi : DirichletCharacter ℂ (2*k.natAbs) → ι → ℂ := fun chi i =>
        let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0
        parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha F.residual
          (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)
      let physical : ι → Prop := fun i =>
        ∃ en : ℕ, Odd en ∧ 0 < en ∧
          ∃ n : ℕ,
            n∈parityOriginalHistoricalFullNEnvelope434 V ∧
            (mp i,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
              d L band slot δ (Nat.ceil (6*U*V)) en (m i) K
              (parityOriginalHistoricalFullNEnvelope434 V) k
              (parityOriginalHistoricalActualZDyadicScale434 (z i)) ∧
            parityOriginalHistoricalCanonicalZ434 en (m i) (mp i) n=z i
      let t : ι → EuclideanSpace ℝ (Fin 3) := fun i =>
        parityOriginalHistoricalRealLogTriple434 U Z (m i) (mp i) (z i)
      let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hLw U E V Z k buf a b hSmooth hBufSupport
      ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
          parityOriginal3DPhysicalFiniteTwistedSource434
            (s.filter physical) Wproj t f ζ‖ ≤
      ‖∑chi : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs chi *
            (∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
              parityOriginal3DPhysicalFiniteTwistedSource434
                s (Wchi chi) t f ζ)‖ +
      parityOriginal3DPhysicalFiniteCoefficientMass434
        ((s.filter good).filter (fun i => ¬physical i)) Wproj *
        (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) := by
  filter_upwards [parity_eventually_original_full_chi_actual_B633_ball_le_signed_correlator434
      S beta gamma Ck hS hbeta hgamma,
    parity_eventually_original_unrestricted_actual_B633_full_chi_carrier_filter434
      S beta gamma Ck hS hbeta hgamma] with L hOldL hIndexL
  refine ⟨hOldL.1,?_⟩
  intro hLw prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ hDyad
    ι decι s m mp z zp hCarrier buf a b hSmooth hBufSupport H T hT
  dsimp only
  classical
  let good : ι → Prop := fun i => m i∈K ∧ mp i∈K ∧ m i≠mp i
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let A : ι → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    (m i) (mp i) (z i) (zp i)
  let Wproj : ι → ℂ := fun i => A i*alpha (m i)*star (alpha (mp i))*
    (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
     then (1:ℂ) else 0)
  let Wchi : DirichletCharacter ℂ (2*k.natAbs) → ι → ℂ := fun chi i =>
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
      (2*k.natAbs) chi 0 0
    parityOriginalHistoricalB633PhysicalPairTerm434
      L rho xi1 xi2 xi3 signed alpha F.residual
      (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)
  let physical : ι → Prop := fun i =>
    ∃ en : ℕ, Odd en ∧ 0 < en ∧ ∃ n : ℕ,
      n∈parityOriginalHistoricalFullNEnvelope434 V ∧
      (mp i,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ (Nat.ceil (6*U*V)) en (m i) K
        (parityOriginalHistoricalFullNEnvelope434 V) k
        (parityOriginalHistoricalActualZDyadicScale434 (z i)) ∧
      parityOriginalHistoricalCanonicalZ434 en (m i) (mp i) n=z i
  let t : ι → EuclideanSpace ℝ (Fin 3) := fun i =>
    parityOriginalHistoricalRealLogTriple434 U Z (m i) (mp i) (z i)
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf a b hSmooth hBufSupport
  have hCarrierGood : ∀i∈s.filter good,
      0 < m i ∧ 0 < mp i ∧ 0 < z i ∧ 0 < zp i ∧
      m i∈K ∧ mp i∈K ∧ m i≠mp i ∧
      (z i:ℤ)+2*k=(zp i:ℤ) ∧
      mp i∣sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (z i) ∧
      m i∣sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (zp i) := by
    intro i hi
    have hs := (Finset.mem_filter.mp hi).1
    obtain ⟨hmK,hmpK,hNe⟩ := (Finset.mem_filter.mp hi).2
    rcases hCarrier i hs with ⟨hm,hmp,hz,hzp,hShift,hDivMp,hDivM⟩
    exact ⟨hm,hmp,hz,hzp,hmK,hmpK,hNe,hShift,hDivMp,hDivM⟩
  have hBound := hOldL.2 hLw prime l u hl hlow K k hk hkBound
    d band slot δ ξ rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ hDyad
    (s.filter good) m mp z zp hCarrierGood
    buf a b hSmooth hBufSupport H T hT
  have hIndex := hIndexL.2 prime l u hl hlow K k hk hkBound
    d band slot δ ξ rho xi1 xi2 xi3 signed s m mp z zp t f T
  have hPhysFilter := parity_original_actual_odd_projector_ball_carrier_filter434
    (s.filter physical) K (b629ActualFineAlpha434 prime L S gamma l u)
    k m mp A t f T
  have hSwap : (s.filter physical).filter good =
      (s.filter good).filter physical := by
    ext i
    simp only [Finset.mem_filter]
    tauto
  change (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434 (s.filter physical) Wproj t f ζ) =
    (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434
        ((s.filter physical).filter good) Wproj t f ζ) at hPhysFilter
  rw [hSwap] at hPhysFilter
  change (∑chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434 s (Wchi chi) t f ζ)) =
    (∑chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434
          (s.filter good) (Wchi chi) t f ζ)) at hIndex
  dsimp only at hBound
  rw [← hPhysFilter, ← hIndex] at hBound
  exact hBound
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqB633DoubleCofactor -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 3600000

/-- Exact ORIGINAL Parity (4.16) double cofactor divisor expansion at
positive z,z+2k, with both reserved-Q/B509 prime residuals, the
identical W1 and parity factors and the actual original h=-2 shift.
The source definition contains no physical e,n gate and no spurious
positive-correlation inequality. -/
def parityOriginalHistoricalActualB633DoubleCofactor434
    (L rho xi1 xi2 xi3 Z : ℝ) (k : ℤ) (N : Finset ℕ)
    (alpha residual : ℕ → ℂ) (q : ℕ)
    (chi : DirichletCharacter ℂ q) (lo hi : ℕ)
    (signed : Bool) (psi : ℝ → ℂ) : ℂ :=
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  ∑ z ∈ N,
    if 0 < (z : ℤ)+2*k then
      let zp := ((z : ℤ)+2*k).toNat
      psi ((z:ℝ)/Z) *
        (∑ mp ∈ (sourceOriginalOrdinaryPart P z).divisors,
          ∑ m ∈ (sourceOriginalOrdinaryPart P zp).divisors,
            parityOriginalHistoricalB633PhysicalPairTerm434
              L rho xi1 xi2 xi3 signed alpha residual q chi lo hi
              m mp z zp)
    else 0

/-- Full unrestricted original Parity z-sum is literally the finite double
cofactor sum of its native B633 pair atoms, BEFORE the χ projector.
Every m,m',z,z+2k divisor and actual prime H0 / W1 / epsilon stays
in the RHS. No artificial source-specified positive e or n. -/
theorem parity_original_historical_actual_B633_double_cofactor_eq_physical434
    (L rho xi1 xi2 xi3 Z : ℝ) (k : ℤ) (N : Finset ℕ)
    (alpha residual : ℕ → ℂ) (q : ℕ)
    (chi : DirichletCharacter ℂ q) (lo hi : ℕ)
    (signed : Bool) (psi : ℝ → ℂ) :
    parityOriginalHistoricalActualB633DoubleCofactor434
      L rho xi1 xi2 xi3 Z k N alpha residual q chi lo hi signed psi =
    parityOriginalEq417PhysicalCofactors434
      L rho xi1 xi2 xi3 0 Z k N alpha residual q chi lo hi signed psi := by
  unfold parityOriginalHistoricalActualB633DoubleCofactor434
    parityOriginalEq417PhysicalCofactors434
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : 0 < (z:ℤ)+2*k
  · simp only [h, ite_true]
    congr 1
  · simp [h]

/-- The *same* original complete double-cofactor sum equals Parity(4.17)
F(z) G(z+2k) with its native signed W1 and both parity factors,
provided exactly the existing source-prime and actual rough-alpha
conditions. This is purely an identity, not a claimed saving on an
arbitrary subset of complex terms. -/
theorem parity_original_historical_actual_B633_double_cofactor_eq_417434
    (L rho xi1 xi2 xi3 Z : ℝ) (k : ℤ) (N : Finset ℕ)
    (hN : ∀ z∈N,0<z)
    (alpha residual : ℕ → ℂ) (q : ℕ)
    (chi : DirichletCharacter ℂ q) (lo hi : ℕ)
    (signed : Bool) (psi : ℝ → ℂ) (W : ℝ)
    (hp : ∀ g p, p ∈ sourceOriginalPAllActualBands 20 L g → p.Prime)
    (hW : ∀ g p, p ∈ sourceOriginalPAllActualBands 20 L g → (p:ℝ) ≤ W)
    (hrough : ∀ m, alpha m ≠ 0 → sourceD20Rough W m) :
    parityOriginalHistoricalActualB633DoubleCofactor434
      L rho xi1 xi2 xi3 Z k N alpha residual q chi lo hi signed psi =
    parityOriginalEq417WithFirstCore434 L rho xi3 Z k N
      (b633ParityFirstCore434 alpha residual q chi lo hi xi2 rho 0)
      (b633ParitySecondCore434 alpha residual q chi lo hi xi1 rho 0)
      signed psi := by
  rw [parity_original_historical_actual_B633_double_cofactor_eq_physical434]
  exact parity_original_eq417_physical_cofactors_exact434 L rho xi1 xi2 xi3 0 Z k N hN
    alpha residual q chi lo hi signed psi W hp hW hrough
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqB633ThreeFourierShift -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 3600000

/-- Fourier scale phases for the REAL original three-logarithm
physical Parity(4.14) pullback, with both U factors and one Z factor.
This is independent of m,m',z and the residual/character labels. -/
def parityOriginalHistoricalB633ThreeFourierScale434
    (U Z : ℝ) (ζ : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  parityOriginalHistoricalFourierScalePhase434 U (ζ 0) *
  parityOriginalHistoricalFourierScalePhase434 U (ζ 1) *
  parityOriginalHistoricalFourierScalePhase434 Z (ζ 2)

/-- At every REAL Fourier frequency, the THREE original Parity
normalized log-phases are exactly equivalent to shifting the
three real powers ξ_1, ξ_2, ξ_3 by 2π times the Fourier frequency.
The cofactor χ, the original B509 residual, W1(z)W1(z+2k),
parity signs, rho-Mellin phases, and the original h=-2 z shift
are UNCHANGED; no source gate or coefficient redefinition occurs.
Positive original m,m',z is the only arithmetic precondition. -/
theorem parity_original_historical_literal_B633_pair_three_fourier_shift434
    (L rho xi1 xi2 xi3 U Z : ℝ)
    (m mp z zp : ℕ) (signed : Bool)
    (alpha residual : ℕ → ℂ) (q : ℕ)
    (chi : DirichletCharacter ℂ q) (lo hi : ℕ)
    (ζ : EuclideanSpace ℝ (Fin 3))
    (hU : 0 < U) (hZ : 0 < Z)
    (hm : 0 < m) (hmp : 0 < mp) (hz : 0 < z) :
    parityOriginalHistoricalB633PhysicalPairTerm434
      L rho xi1 xi2 xi3 signed alpha residual q chi lo hi m mp z zp *
      parityOriginal3DPhysicalLogFourierPhase434 ζ
        (parityOriginalHistoricalRealLogTriple434 U Z m mp z) =
    parityOriginalHistoricalB633ThreeFourierScale434 U Z ζ *
      parityOriginalHistoricalB633PhysicalPairTerm434
        L rho (xi1+2*Real.pi*(ζ 0))
          (xi2+2*Real.pi*(ζ 1)) (xi3+2*Real.pi*(ζ 2))
          signed alpha residual q chi lo hi m mp z zp := by
  rw [parity_original_historical_three_log_phases_to_parity_416434
        U Z hU hZ m mp z hm hmp hz ζ]
  unfold parityOriginalHistoricalB633ThreeFourierScale434
    parityOriginalHistoricalB633PhysicalPairTerm434
  rw [parity_original_physical_imaginary_power_add434 m hm xi1 (2*Real.pi*(ζ 0)),
      parity_original_physical_imaginary_power_add434 mp hmp xi2 (2*Real.pi*(ζ 1)),
      parity_original_physical_imaginary_power_add434 z hz xi3 (2*Real.pi*(ζ 2))]
  ring

/-- Exact three-log Fourier normalization has unit modulus; the
fixed scale phases cannot worsen original Parity(4.17) signed saving. -/
theorem parity_original_historical_B633_three_fourier_scale_norm_one434
    (U Z : ℝ) (ζ : EuclideanSpace ℝ (Fin 3)) :
    ‖parityOriginalHistoricalB633ThreeFourierScale434 U Z ζ‖=1 := by
  have hScale (W ν : ℝ) :
      ‖parityOriginalHistoricalFourierScalePhase434 W ν‖=1 := by
    unfold parityOriginalHistoricalFourierScalePhase434
    rw [mul_comm Complex.I]
    exact Complex.norm_exp_ofReal_mul_I _
  unfold parityOriginalHistoricalB633ThreeFourierScale434
  rw [norm_mul, norm_mul, hScale, hScale, hScale]
  norm_num
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqB633FullFourierCofactor -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 3800000

/-- EXACT source Parity4.16 unrestricted double prime-slot cofactor sum
at one genuine Fourier frequency ζ, including original smooth ψ(z/Z),
all m,m' ordinary-divisor cores, original shift z+2k and sigma=0.
No source (e,n) sharp gates and no alpha=0 terms discarded. -/
def parityOriginalHistoricalActualB633FullFourierCofactor434
    (L rho xi1 xi2 xi3 U Z : ℝ) (k : ℤ) (N : Finset ℕ)
    (alpha residual : ℕ → ℂ) (q : ℕ)
    (chi : DirichletCharacter ℂ q) (lo hi : ℕ)
    (signed : Bool) (psi : ℝ → ℂ)
    (ζ : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  ∑ z ∈ N,
    if 0 < (z : ℤ)+2*k then
      let zp := ((z : ℤ)+2*k).toNat
      psi ((z:ℝ)/Z) *
        (∑ mp ∈ (sourceOriginalOrdinaryPart P z).divisors,
          ∑ m ∈ (sourceOriginalOrdinaryPart P zp).divisors,
            parityOriginalHistoricalB633PhysicalPairTerm434
              L rho xi1 xi2 xi3 signed alpha residual q chi lo hi
              m mp z zp *
            parityOriginal3DPhysicalLogFourierPhase434 ζ
              (parityOriginalHistoricalRealLogTriple434 U Z m mp z))
    else 0

/-- UNIVERSAL original full z,m,m' Fourier-to-Parity4.16 exact identity.
The entire ψ weighted original B633 double-divisor sum at ζ is the
one source-normalization phase (norm one) multiplied by the same
unrestricted B633 sum with ξ1,ξ2,ξ3 shifted by exactly 2πζj.
No χ, ε, skipped-Q/H0, W1 or rho factors are dropped; the only
arithmetic premise is each z∈N positive (every m,m' divisor is
then automatically a positive natural number). -/
theorem parity_original_historical_actual_B633_full_cofactor_fourier_shift434
    (L rho xi1 xi2 xi3 U Z : ℝ) (k : ℤ) (N : Finset ℕ)
    (hN : ∀z∈N,0 < z)
    (alpha residual : ℕ → ℂ) (q : ℕ)
    (chi : DirichletCharacter ℂ q) (lo hi : ℕ)
    (signed : Bool) (psi : ℝ → ℂ)
    (ζ : EuclideanSpace ℝ (Fin 3))
    (hU : 0 < U) (hZ : 0 < Z) :
    parityOriginalHistoricalActualB633FullFourierCofactor434
      L rho xi1 xi2 xi3 U Z k N alpha residual q chi lo hi signed psi ζ =
    parityOriginalHistoricalB633ThreeFourierScale434 U Z ζ *
      parityOriginalHistoricalActualB633DoubleCofactor434
        L rho (xi1+2*Real.pi*(ζ 0))
          (xi2+2*Real.pi*(ζ 1)) (xi3+2*Real.pi*(ζ 2)) Z k N
        alpha residual q chi lo hi signed psi := by
  unfold parityOriginalHistoricalActualB633FullFourierCofactor434
    parityOriginalHistoricalActualB633DoubleCofactor434
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hshift : 0 < (z:ℤ)+2*k
  · simp only [hshift,ite_true]
    let zp := ((z:ℤ)+2*k).toNat
    let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
    have hinner :
        (∑mp∈(sourceOriginalOrdinaryPart P z).divisors,
          ∑m∈(sourceOriginalOrdinaryPart P zp).divisors,
            parityOriginalHistoricalB633PhysicalPairTerm434
              L rho xi1 xi2 xi3 signed alpha residual q chi lo hi m mp z zp *
            parityOriginal3DPhysicalLogFourierPhase434 ζ
              (parityOriginalHistoricalRealLogTriple434 U Z m mp z)) =
        parityOriginalHistoricalB633ThreeFourierScale434 U Z ζ *
        (∑mp∈(sourceOriginalOrdinaryPart P z).divisors,
          ∑m∈(sourceOriginalOrdinaryPart P zp).divisors,
            parityOriginalHistoricalB633PhysicalPairTerm434
              L rho (xi1+2*Real.pi*(ζ 0))
                (xi2+2*Real.pi*(ζ 1)) (xi3+2*Real.pi*(ζ 2))
                signed alpha residual q chi lo hi m mp z zp) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro mp hmp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hPosMp : 0 < mp := Nat.pos_of_mem_divisors hmp
      have hPosM : 0 < m := Nat.pos_of_mem_divisors hm
      exact parity_original_historical_literal_B633_pair_three_fourier_shift434
        L rho xi1 xi2 xi3 U Z m mp z zp signed alpha residual
        q chi lo hi ζ hU hZ hPosM hPosMp (hN z hz)
    change psi ((z:ℝ)/Z) *
        (∑mp∈(sourceOriginalOrdinaryPart P z).divisors,
          ∑m∈(sourceOriginalOrdinaryPart P zp).divisors,
            parityOriginalHistoricalB633PhysicalPairTerm434
              L rho xi1 xi2 xi3 signed alpha residual q chi lo hi m mp z zp *
            parityOriginal3DPhysicalLogFourierPhase434 ζ
              (parityOriginalHistoricalRealLogTriple434 U Z m mp z)) =
      parityOriginalHistoricalB633ThreeFourierScale434 U Z ζ *
        (psi ((z:ℝ)/Z) *
          (∑mp∈(sourceOriginalOrdinaryPart P z).divisors,
            ∑m∈(sourceOriginalOrdinaryPart P zp).divisors,
              parityOriginalHistoricalB633PhysicalPairTerm434
                L rho (xi1+2*Real.pi*(ζ 0))
                  (xi2+2*Real.pi*(ζ 1)) (xi3+2*Real.pi*(ζ 2))
                  signed alpha residual q chi lo hi m mp z zp))
    rw [hinner]
    ring
  · simp only [hshift, ite_false, mul_zero]

/-- Exact **original Parity(4.17)** identification after genuine
3D Fourier separation, with full (z,m,m') unrestricted source,
actual prime-slot residual and character q, and the right 2π
frequency shifts. This theorem is an *identity*, not a hypothetical
signed saving or an assertion about the physical (e,n) subfamily. -/
theorem parity_original_historical_actual_B633_full_cofactor_fourier_eq_417434
    (L rho xi1 xi2 xi3 U Z : ℝ) (k : ℤ) (N : Finset ℕ)
    (hN : ∀z∈N,0 < z)
    (alpha residual : ℕ → ℂ) (q : ℕ)
    (chi : DirichletCharacter ℂ q) (lo hi : ℕ)
    (signed : Bool) (psi : ℝ → ℂ)
    (ζ : EuclideanSpace ℝ (Fin 3))
    (hU : 0 < U) (hZ : 0 < Z) (W : ℝ)
    (hp : ∀ g p, p ∈ sourceOriginalPAllActualBands 20 L g → p.Prime)
    (hW : ∀ g p, p ∈ sourceOriginalPAllActualBands 20 L g → (p:ℝ) ≤ W)
    (hrough : ∀m, alpha m ≠ 0 → sourceD20Rough W m) :
    parityOriginalHistoricalActualB633FullFourierCofactor434
      L rho xi1 xi2 xi3 U Z k N alpha residual q chi lo hi signed psi ζ =
    parityOriginalHistoricalB633ThreeFourierScale434 U Z ζ *
      parityOriginalEq417WithFirstCore434 L rho (xi3+2*Real.pi*(ζ 2)) Z k N
        (b633ParityFirstCore434 alpha residual q chi lo hi
          (xi2+2*Real.pi*(ζ 1)) rho 0)
        (b633ParitySecondCore434 alpha residual q chi lo hi
          (xi1+2*Real.pi*(ζ 0)) rho 0)
        signed psi := by
  rw [parity_original_historical_actual_B633_full_cofactor_fourier_shift434
      L rho xi1 xi2 xi3 U Z k N hN alpha residual q chi lo hi
      signed psi ζ hU hZ]
  rw [parity_original_historical_actual_B633_double_cofactor_eq_417434
      L rho (xi1+2*Real.pi*(ζ 0)) (xi2+2*Real.pi*(ζ 1))
      (xi3+2*Real.pi*(ζ 2)) Z k N hN alpha residual q chi lo hi
      signed psi W hp hW hrough]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqB633FourierEq417Saving -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4500000

/-- ORIGINAL r0=20, h=-2, real B509 residual, fine b629 prime/proxy
coefficient, literal signed epsilon/W1, true ψ_Z and full UNRESTRICTED
B633 double-cofactor (z,m,m') sum: arbitrary inverse-log saving at ONE
real 3D Fourier frequency, for EVERY original character χ mod 2|k|.

This is a genuine application of the already PROVED unrestricted Parity
(4.17) specialized physical-cofactor estimate, not an axiom, conditional
signed-subset inequality or abstract bounded-amplitude contract.
The three SOURCE powers are shifted by exactly 2πζ_j, with the same
real theta/rho and σ=0 skipped-Q residual and the original 2k shift.
The source hypotheses require precisely the shifted frequencies to lie
inside the Parity(4.17) logarithmic frequency budget. The full χ-outer
and Fourier family sums and physical source-to-cofactor reindex are
separate, still-unproved global obligations. -/
theorem parity_eventually_original_actual_B633_full_fourier_fixed_chi_saving434
    (jQ : ℕ) (target Cfreq CZ Ck beta gamma : ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck)
    (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (chi : DirichletCharacter ℂ (2*k.natAbs))
          (rho xi1 xi2 xi3 U : ℝ)
          (ζ : EuclideanSpace ℝ (Fin 3)),
          0 < U → |rho| ≤ L^Cfreq →
          |xi1+2*Real.pi*(ζ 0)| ≤ L^Cfreq →
          |xi2+2*Real.pi*(ζ 1)| ≤ L^Cfreq →
          |xi3+2*Real.pi*(ζ 2)| ≤ L^Cfreq →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine →
          (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (signed : Bool),
        let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L)
          L band slot delta freq (Finset.Icc a b)
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
          (2*k.natAbs) chi 0 0
        let N := Finset.Icc 1 ⌊64*Z⌋₊
        let original := parityOriginalHistoricalActualB633FullFourierCofactor434
          L rho xi1 xi2 xi3 U Z k N F.alpha F.residual
          (2*k.natAbs) chi F.lo F.hi signed
          parityOriginalHistoricalDyadicSmoothPsi434 ζ
        ‖original‖ ≤ Z*L^(-target) := by
  obtain ⟨Kpsi,hKpsi,hPsiBudget⟩ :=
    parity_original_historical_fixed_smooth_dyadic_psi_log_budget434
  obtain ⟨J,B,S,hSB,hSave⟩ :=
    parity_eventually_actual_original_Parity417_physical_cofactor_saving434
      jQ target Cfreq CZ Ck 0 beta gamma Kpsi
      hTarget hCZ hCk (by norm_num) hKpsi hbeta hgamma
  refine ⟨J,B,S,hSB,?_⟩
  filter_upwards [hSave,eventually_ge_atTop (1:ℝ)] with L hSaveL hL
  refine ⟨hSaveL.1,hSaveL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
    chi rho xi1 xi2 xi3 U ζ hU hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu hub signed
  dsimp only
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L
    band slot delta freq (Finset.Icc a b)
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let N : Finset ℕ := Finset.Icc 1 ⌊64*Z⌋₊
  let psi : ℝ → ℂ := parityOriginalHistoricalDyadicSmoothPsi434
  let original := parityOriginalHistoricalActualB633FullFourierCofactor434
    L rho xi1 xi2 xi3 U Z k N F.alpha F.residual
    (2*k.natAbs) chi F.lo F.hi signed psi ζ
  let shifted := parityOriginalEq417PhysicalCofactors434
    L rho (xi1+2*Real.pi*(ζ 0)) (xi2+2*Real.pi*(ζ 1))
      (xi3+2*Real.pi*(ζ 2)) 0 Z k N F.alpha F.residual
      (2*k.natAbs) chi F.lo F.hi signed psi
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hL
  have hZpos : 0 < Z := by
    have h : 0 < Real.exp L*L^(-CZ) :=
      mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLpos _)
    exact h.trans_le hZlo
  have hN : ∀ z∈N,0 < z := by
    intro z hz
    exact (Finset.mem_Icc.mp hz).1
  have h0 : |(0:ℝ)| ≤ L^Cfreq := by
    simpa only [abs_zero] using (Real.rpow_nonneg hLpos.le Cfreq)
  have hBound : ‖shifted‖ ≤ Z*L^(-target) :=
    hSaveL.2.2 hFamily Z hZlo hZhi band hband slot delta freq
      k hk hkBound chi rho
      (xi1+2*Real.pi*(ζ 0)) (xi2+2*Real.pi*(ζ 1))
      (xi3+2*Real.pi*(ζ 2)) 0 hrho hxi1 hxi2 hxi3 h0
      prime lFine uFine a b hFineLow hl hu hub signed psi
      parity_original_historical_dyadic_smooth_psi_contDiff434
      parity_original_historical_dyadic_psi_Parity417_support434
      (hPsiBudget L)
  have hExp : original =
      parityOriginalHistoricalB633ThreeFourierScale434 U Z ζ * shifted := by
    dsimp [original,shifted]
    rw [parity_original_historical_actual_B633_full_cofactor_fourier_shift434
      L rho xi1 xi2 xi3 U Z k N hN F.alpha F.residual
      (2*k.natAbs) chi F.lo F.hi signed psi ζ hU hZpos]
    congr 1
  change ‖original‖ ≤ Z*L^(-target)
  rw [hExp,norm_mul,parity_original_historical_B633_three_fourier_scale_norm_one434,one_mul]
  exact hBound
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqB633FullChiFourierSaving -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4500000

/-- ACTUAL ORIGINAL Parity (4.17) full finite cofactor *and full character*
Fourier signed saving for r0=20, h=-2, actual b629 fine alpha,
B509 reserved-Q H0, W1 and parity at both endpoints, fixed ψ_Z.
For any target D>0, choose the original J,B,S before L, z, k,
character, Fourier frequency, fine interval and physical coefficients;
there is NO extra #χ factor because the ORIGINAL mod 2|k| mask has
ℓ1 mass at most 1. The three Fourier twists shift ξ_j by 2πζ_j.
No unknown per-character saving is assumed: it is invoked from the
native unconditional source Parity (4.17) proof.
This remains the unrestricted (z,m,m') correlator; connecting it to
the physical B-prime (e,n) full Fourier outer is a separate lemma. -/
theorem parity_eventually_original_actual_B633_full_chi_fourier_saving434
    (jQ : ℕ) (target Cfreq CZ Ck beta gamma : ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck)
    (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (rho xi1 xi2 xi3 U : ℝ)
          (ζ : EuclideanSpace ℝ (Fin 3)),
          0 < U → |rho| ≤ L^Cfreq →
          |xi1+2*Real.pi*(ζ 0)| ≤ L^Cfreq →
          |xi2+2*Real.pi*(ζ 1)| ≤ L^Cfreq →
          |xi3+2*Real.pi*(ζ 2)| ≤ L^Cfreq →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine →
          (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (signed : Bool),
        let N := Finset.Icc 1 ⌊64*Z⌋₊
        let F : DirichletCharacter ℂ (2*k.natAbs) → PrimeSlotCore := fun chi =>
          sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L)
            L band slot delta freq (Finset.Icc a b)
            (b629ActualFineAlpha434 prime L S gamma lFine uFine)
            (2*k.natAbs) chi 0 0
        let original := ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs chi *
            parityOriginalHistoricalActualB633FullFourierCofactor434
              L rho xi1 xi2 xi3 U Z k N (F chi).alpha (F chi).residual
              (2*k.natAbs) chi (F chi).lo (F chi).hi signed
              parityOriginalHistoricalDyadicSmoothPsi434 ζ
        ‖original‖ ≤ Z*L^(-target) := by
  obtain ⟨J,B,S,hSB,hEachL⟩ :=
    parity_eventually_original_actual_B633_full_fourier_fixed_chi_saving434
      jQ target Cfreq CZ Ck beta gamma hTarget hCZ hCk hbeta hgamma
  refine ⟨J,B,S,hSB,?_⟩
  filter_upwards [hEachL,eventually_ge_atTop (1:ℝ)] with L hEachL hL
  refine ⟨hEachL.1,hEachL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
    rho xi1 xi2 xi3 U ζ hU hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu hub signed
  dsimp only
  let N := Finset.Icc 1 ⌊64*Z⌋₊
  let F : DirichletCharacter ℂ (2*k.natAbs) → PrimeSlotCore := fun chi =>
    sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L)
      L band slot delta freq (Finset.Icc a b)
      (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      (2*k.natAbs) chi 0 0
  let W : DirichletCharacter ℂ (2*k.natAbs) → ℂ := fun chi =>
    parityOriginalHistoricalActualB633FullFourierCofactor434
      L rho xi1 xi2 xi3 U Z k N (F chi).alpha (F chi).residual
      (2*k.natAbs) chi (F chi).lo (F chi).hi signed
      parityOriginalHistoricalDyadicSmoothPsi434 ζ
  have hAll (chi : DirichletCharacter ℂ (2*k.natAbs)) :
      ‖W chi‖ ≤ Z*L^(-target) := by
    exact hEachL.2.2 hFamily Z hZlo hZhi band hband slot delta freq
      k hk hkBound chi rho xi1 xi2 xi3 U ζ hU hrho hxi1 hxi2 hxi3
      prime lFine uFine a b hFineLow hl hu hub signed
  have hZpos : 0 < Z := by
    have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hL
    have h : 0 < Real.exp L*L^(-CZ) :=
      mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLpos _)
    exact h.trans_le hZlo
  have hM : 0 ≤ Z*L^(-target) :=
    (mul_nonneg hZpos.le (Real.rpow_nonneg (le_trans (by norm_num : (0:ℝ)≤1) hL) _))
  change ‖∑ chi : DirichletCharacter ℂ (2*k.natAbs),
    parityShiftTwoMaskCoefficient434 k.natAbs chi * W chi‖ ≤ Z*L^(-target)
  calc
    _ ≤ ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
        ‖parityShiftTwoMaskCoefficient434 k.natAbs chi * W chi‖ := norm_sum_le _ _
    _ ≤ ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
        ‖parityShiftTwoMaskCoefficient434 k.natAbs chi‖ * (Z*L^(-target)) := by
          apply Finset.sum_le_sum
          intro chi hchi
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hAll chi) (norm_nonneg _)
    _ = (Z*L^(-target)) *
        (∑ chi : DirichletCharacter ℂ (2*k.natAbs),
          ‖parityShiftTwoMaskCoefficient434 k.natAbs chi‖) := by
          rw [←Finset.sum_mul]
          ring
    _ ≤ (Z*L^(-target))*1 :=
      mul_le_mul_of_nonneg_left
        (parity_signed_shift_two_mask_coefficient_mass_le_one434 k hk) hM
    _ = _ := mul_one _
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqB633FullSigmaIndex -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2900000

/-- The genuine UNRESTRICTED original Parity (4.16)--(4.17)
three-index carrier: for each z in the positive native z-set,
m' divides the actual P-ordinary core of z and m divides the
P-ordinary core of z+2k. Sigma index, not an artificial set of
source (e,n) occurrences: no dedup or cardinality loss. -/
def parityOriginalHistoricalActualB633FullSigmaIndex434
    (L : ℝ) (k : ℤ) (N : Finset ℕ) :
    Finset (Σ z : ℕ, Σ mp : ℕ, ℕ) :=
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  N.sigma (fun z =>
    (sourceOriginalOrdinaryPart P z).divisors.sigma (fun _mp =>
      (sourceOriginalOrdinaryPart P (((z:ℤ)+2*k).toNat)).divisors))

/-- EXACT original unrestricted three-cofactor reindex for any
complex amplitude A(z,m',m), even with cancellations, zeros and
multiple ordinary-P divisors. The finite dependent Sigma type
counts each (z,m',m) once; no division by multiplicity or
positive-subset comparison is made. -/
theorem parity_original_historical_full_sigma_cofactor_reindex434
    (L : ℝ) (k : ℤ) (N : Finset ℕ)
    (A : ℕ → ℕ → ℕ → ℂ) :
    (∑z∈N,
      ∑mp∈(sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) z).divisors,
        ∑m∈(sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L))
          (((z:ℤ)+2*k).toNat)).divisors, A z mp m) =
    ∑i∈parityOriginalHistoricalActualB633FullSigmaIndex434 L k N,
      A i.1 i.2.1 i.2.2 := by
  classical
  simp only [parityOriginalHistoricalActualB633FullSigmaIndex434,
    Finset.sum_sigma]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqB633FullSigmaExpansion -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- EXACT original Parity (4.16)-(4.17) full z,m',m double-divisor
sum as one finite Sigma index, retaining ψ(z/Z), source real shift
z+2k and all original B509 H0, α, χ, W1 and signed ε in the
literal pair atom. The positivity test stays inside each atom:
no complex signed sub-sum or nonphysical (e,n) filter is removed.
This is the concrete complete cofactor set on which the WHOLE
original χ projector may be formed before source filtering. -/
theorem parity_original_historical_B633_full_sigma_exact_expansion434
    (L rho xi1 xi2 xi3 Z : ℝ) (k : ℤ) (N : Finset ℕ)
    (alpha residual : ℕ → ℂ) (q : ℕ)
    (chi : DirichletCharacter ℂ q) (lo hi : ℕ)
    (signed : Bool) (psi : ℝ → ℂ) :
    parityOriginalHistoricalActualB633DoubleCofactor434
      L rho xi1 xi2 xi3 Z k N alpha residual q chi lo hi signed psi =
    ∑i∈parityOriginalHistoricalActualB633FullSigmaIndex434 L k N,
      if 0 < (i.1:ℤ)+2*k then
        psi ((i.1:ℝ)/Z) *
          parityOriginalHistoricalB633PhysicalPairTerm434
            L rho xi1 xi2 xi3 signed alpha residual q chi lo hi
            i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
      else 0 := by
  classical
  let A : ℕ → ℕ → ℕ → ℂ := fun z mp m =>
    if 0 < (z:ℤ)+2*k then
      psi ((z:ℝ)/Z) *
        parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha residual q chi lo hi
          m mp z (((z:ℤ)+2*k).toNat)
    else 0
  have hIndex := parity_original_historical_full_sigma_cofactor_reindex434 L k N A
  change (∑z∈N,
    if 0 < (z:ℤ)+2*k then
      let zp := (((z:ℤ)+2*k).toNat)
      psi ((z:ℝ)/Z) *
        (∑mp∈(sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) z).divisors,
          ∑m∈(sourceOriginalOrdinaryPart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) zp).divisors,
            parityOriginalHistoricalB633PhysicalPairTerm434
              L rho xi1 xi2 xi3 signed alpha residual q chi lo hi
              m mp z zp)
    else 0) = _
  rw [← hIndex]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hshift : 0 < (z:ℤ)+2*k
  · simp only [hshift,ite_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro mp hmp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    simp [A,hshift]
  · simp [A,hshift]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqPsiWeightedChiBall -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- The ORIGINAL Parity (4.16) whole-character projective Fourier-ball
identity with an ARBITRARY complex index-dependent weight g_i. This
allows the LITERAL smooth dyadic ψ(z/Z) to be inserted BEFORE
Fourier-ball truncation and character summation, preserving every
original core, signed epsilon, H0 residual, and nonlinear Schwartz
η_eη_n, and does not assume that a complex subfamily is monotone.
For g_i=ψ(z_i/Z) this is precisely the source-relevant extension.
No source e,n image equality or spectral saving is claimed. -/
theorem parity_eventually_original_unrestricted_actual_B633_psi_weighted_projected_fourier_ball434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (rho xi1 xi2 xi3 : ℝ) (signed : Bool)
        {ι : Type} [DecidableEq ι] (s : Finset ι)
        (m mp z zp : ι → ℕ)
        (g : ι → ℂ)
        (t : ι → EuclideanSpace ℝ (Fin 3))
        (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) (R : ℝ),
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let A : ι → ℂ := fun i => g i * parityOriginalHistoricalB633CharacterFreeAtom434
        L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
        (m i) (mp i) (z i) (zp i)
      let Wodd : ι → ℂ := fun i => A i*alpha (m i)*star (alpha (mp i))*
        (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
          then (1:ℂ) else 0)
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤R}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434 s Wodd t f ζ) =
      ∑chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi *
        (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤R}:Set _),
          parityOriginal3DPhysicalFiniteTwistedSource434 s
            (fun i => g i *
              (let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
                (2*k.natAbs) chi 0 0
              parityOriginalHistoricalB633PhysicalPairTerm434
                L rho xi1 xi2 xi3 signed alpha F.residual
                (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)))
            t f ζ) := by
  filter_upwards [parity_eventually_original_actual_alpha_odd_e_projected_fourier_ball434
    S beta gamma Ck hS hbeta hgamma] with L hProj
  refine ⟨hProj.1,?_⟩
  intro prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 signed ι decι s m mp z zp g t f R
  dsimp only
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let A : ι → ℂ := fun i => g i * parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    (m i) (mp i) (z i) (zp i)
  let Wodd : ι → ℂ := fun i => A i*alpha (m i)*star (alpha (mp i))*
    (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
      then (1:ℂ) else 0)
  have hBall := hProj.2 prime l u hl hlow K k hk hkBound
    s m mp A t f R
  dsimp only at hBall
  change (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤R}:Set _),
    parityOriginal3DPhysicalFiniteTwistedSource434 s Wodd t f ζ) = _
  rw [hBall]
  apply Finset.sum_congr rfl
  intro chi hchi
  congr 1
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) chi 0 0
  have hInv := parity_original_historical_B633_reserved_source_chi_invariant434
    d L band slot δ ξ K alpha (2*k.natAbs) chi 1
  have hW : (fun i : ι => (A i*alpha (m i)*star (alpha (mp i))) *
      chi (mp i:ZMod (2*k.natAbs)) *
      star (chi (m i:ZMod (2*k.natAbs)))) =
      (fun i : ι => g i * parityOriginalHistoricalB633PhysicalPairTerm434
        L rho xi1 xi2 xi3 signed alpha F.residual
        (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)) := by
    funext i
    have hChar := parity_original_historical_B633_full_character_factor434
      L rho xi1 xi2 xi3 signed alpha F.residual
      (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)
    rw [hChar]
    dsimp only [A]
    rw [hInv.1,hInv.2.1,hInv.2.2]
    ring
  rw [hW]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqPsiFullCharacterIndexFilter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2500000

/-- Original Parity (4.16) complete character-summed Fourier-ball equality
with arbitrary complex ψ-like weight g(z,m',m), before and after the
ONLY justified cofactor index filters m,m' ∈ K and m != m'.
These filters are removed from the FULL character sum, not from each
individual χ separately. Source alpha, H0, W1 and signed epsilon
remain literal; no n/e physical mask is inserted. -/
theorem parity_eventually_original_unrestricted_actual_B633_psi_full_chi_carrier_filter434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (rho xi1 xi2 xi3 : ℝ) (signed : Bool)
        {ι : Type} [DecidableEq ι] (s : Finset ι)
        (m mp z zp : ι → ℕ)
        (g : ι → ℂ)
        (t : ι → EuclideanSpace ℝ (Fin 3))
        (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) (T : ℝ),
      let good : ι → Prop := fun i => m i∈K ∧ mp i∈K ∧ m i≠mp i
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let A : ι → ℂ := fun i => g i * parityOriginalHistoricalB633CharacterFreeAtom434
        L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
        (m i) (mp i) (z i) (zp i)
      let Wchi : DirichletCharacter ℂ (2*k.natAbs) → ι → ℂ := fun chi i =>
        let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0
        g i * parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha F.residual
          (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)
      (∑chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi *
          (∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
            parityOriginal3DPhysicalFiniteTwistedSource434 s (Wchi chi) t f ζ)) =
      (∑chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi *
          (∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
            parityOriginal3DPhysicalFiniteTwistedSource434
              (s.filter good) (Wchi chi) t f ζ)) := by
  filter_upwards [parity_eventually_original_unrestricted_actual_B633_psi_weighted_projected_fourier_ball434
    S beta gamma Ck hS hbeta hgamma] with L hProj
  refine ⟨hProj.1,?_⟩
  intro prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 signed ι decι s m mp z zp g t f T
  dsimp only
  let good : ι → Prop := fun i => m i∈K ∧ mp i∈K ∧ m i≠mp i
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let A : ι → ℂ := fun i => g i * parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    (m i) (mp i) (z i) (zp i)
  let Wchi : DirichletCharacter ℂ (2*k.natAbs) → ι → ℂ := fun chi i =>
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
      (2*k.natAbs) chi 0 0
    g i * parityOriginalHistoricalB633PhysicalPairTerm434
      L rho xi1 xi2 xi3 signed alpha F.residual
      (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)
  let Wproj : ι → ℂ := fun i => A i*alpha (m i)*star (alpha (mp i))*
    (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
     then (1:ℂ) else 0)
  have hFull := hProj.2 prime l u hl hlow K k hk hkBound
    d band slot δ ξ rho xi1 xi2 xi3 signed s m mp z zp g t f T
  have hRestr := hProj.2 prime l u hl hlow K k hk hkBound
    d band slot δ ξ rho xi1 xi2 xi3 signed (s.filter good)
    m mp z zp g t f T
  have hFilter := parity_original_actual_odd_projector_ball_carrier_filter434
    s K (b629ActualFineAlpha434 prime L S gamma l u) k m mp A t f T
  change (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434 s Wproj t f ζ) =
    (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434 (s.filter good) Wproj t f ζ)
    at hFilter
  change (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434 s Wproj t f ζ) =
    ∑chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434 s (Wchi chi) t f ζ)
    at hFull
  change (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434 (s.filter good) Wproj t f ζ) =
    ∑chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434
          (s.filter good) (Wchi chi) t f ζ)
    at hRestr
  exact hFull.symm.trans (hFilter.trans hRestr)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqPsiWeightGhostFullChiBall -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- Original B633 χ-projected low-frequency Fourier-BALL transfer
with an ARBITRARY complex scalar index weight g_i (particularly
Parity's fixed smooth dyadic ψ(z/Z)). The physical complement has zero
FULL SOURCE Fourier signal only after the exact χ projector, while
its ball is explicitly paid by the true ψ-weighted positive mass
and Schwartz moment/T^H. Original residual H0, W1, ε, actual α,
positive cofactor/divisor carrier and true h=-2 shift remain literal.
No per-character signed-subset inequality or new analytic saving. -/
theorem parity_eventually_original_full_chi_actual_B633_psi_ball_le_signed_correlator434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L) (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (rho xi1 xi2 xi3 U E V Z : ℝ) (signed : Bool),
      0<U → 0<E → 0<V → 0<Z →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
      ∀ {ι : Type} [DecidableEq ι] (s : Finset ι)
        (m mp z zp : ι → ℕ) (g : ι → ℂ),
      (∀ i∈s, 0 < m i ∧ 0 < mp i ∧ 0 < z i ∧ 0 < zp i ∧
        m i ∈ K ∧ mp i ∈ K ∧ m i ≠ mp i ∧
        (z i:ℤ)+2*k=(zp i:ℤ) ∧
        mp i∣sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (z i) ∧
        m i∣sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (zp i)) →
      ∀ (buf : ℝ → ℂ) (a b : ℝ)
        (hSmooth : ContDiff ℝ ∞ buf)
        (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
        (H : ℕ) (T : ℝ), 0<T →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let A : ι → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
        L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
        (m i) (mp i) (z i) (zp i)
      let Wproj : ι → ℂ := fun i => g i * A i*alpha (m i)*star (alpha (mp i))*
        (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
         then (1:ℂ) else 0)
      let Wchi : DirichletCharacter ℂ (2*k.natAbs) → ι → ℂ := fun chi i =>
        let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0
        g i * parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha F.residual
          (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)
      let physical : ι → Prop := fun i =>
        ∃ en : ℕ, Odd en ∧ 0 < en ∧
          ∃ n : ℕ,
            n∈parityOriginalHistoricalFullNEnvelope434 V ∧
            (mp i,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
              d L band slot δ (Nat.ceil (6*U*V)) en (m i) K
              (parityOriginalHistoricalFullNEnvelope434 V) k
              (parityOriginalHistoricalActualZDyadicScale434 (z i)) ∧
            parityOriginalHistoricalCanonicalZ434 en (m i) (mp i) n=z i
      let t : ι → EuclideanSpace ℝ (Fin 3) := fun i =>
        parityOriginalHistoricalRealLogTriple434 U Z (m i) (mp i) (z i)
      let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hLw U E V Z k buf a b hSmooth hBufSupport
      ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
          parityOriginal3DPhysicalFiniteTwistedSource434
            (s.filter physical) Wproj t f ζ‖ ≤
      ‖∑chi : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs chi *
            (∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
              parityOriginal3DPhysicalFiniteTwistedSource434
                s (Wchi chi) t f ζ)‖ +
      parityOriginal3DPhysicalFiniteCoefficientMass434
        (s.filter (fun i => ¬physical i)) Wproj *
        (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) := by
  filter_upwards [parity_eventually_original_full_chi_B633_ghost_weighted_zero434
      S beta gamma Ck hS hbeta hgamma,
    parity_eventually_original_unrestricted_actual_B633_psi_weighted_projected_fourier_ball434
      S beta gamma Ck hS hbeta hgamma] with L hGhostL hProjL
  refine ⟨hGhostL.1,?_⟩
  intro hLw prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ hDyad
    ι decι s m mp z zp g hCarrier buf a b hSmooth hBufSupport H T hT
  dsimp only
  classical
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let A : ι → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    (m i) (mp i) (z i) (zp i)
  let Wproj : ι → ℂ := fun i => g i*A i*alpha (m i)*star (alpha (mp i))*
    (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
     then (1:ℂ) else 0)
  let Wchi : DirichletCharacter ℂ (2*k.natAbs) → ι → ℂ := fun chi i =>
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
      (2*k.natAbs) chi 0 0
    g i * parityOriginalHistoricalB633PhysicalPairTerm434
      L rho xi1 xi2 xi3 signed alpha F.residual
      (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)
  let physical : ι → Prop := fun i =>
    ∃ en : ℕ, Odd en ∧ 0 < en ∧ ∃ n : ℕ,
      n∈parityOriginalHistoricalFullNEnvelope434 V ∧
      (mp i,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ (Nat.ceil (6*U*V)) en (m i) K
        (parityOriginalHistoricalFullNEnvelope434 V) k
        (parityOriginalHistoricalActualZDyadicScale434 (z i)) ∧
      parityOriginalHistoricalCanonicalZ434 en (m i) (mp i) n=z i
  let t : ι → EuclideanSpace ℝ (Fin 3) := fun i =>
    parityOriginalHistoricalRealLogTriple434 U Z (m i) (mp i) (z i)
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf a b hSmooth hBufSupport
  have hWeighted : ∀i∈s, ¬physical i → Wproj i*f (t i)=0 := by
    intro i hi hnot
    rcases hCarrier i hi with ⟨hm,hmp,hz,hzp,hmK,hmpK,hNe,hShift,hDivMp,hDivM⟩
    have hZero := hGhostL.2 hLw prime l u hl hlow K k hk hkBound
      d band slot δ ξ rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ hDyad
      (m i) (mp i) (z i) (zp i) hm hmp hz hzp hmK hmpK hNe
      hShift hDivMp hDivM buf a b hSmooth hBufSupport hnot
    change (A i*alpha (m i)*star (alpha (mp i))*
      (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
       then (1:ℂ) else 0))*f (t i)=0 at hZero
    change (g i*A i*alpha (m i)*star (alpha (mp i))*
      (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
       then (1:ℂ) else 0))*f (t i)=0
    calc
      _ = g i * ((A i*alpha (m i)*star (alpha (mp i))*
        (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
         then (1:ℂ) else 0))*f (t i)) := by ring
      _ = 0 := by rw [hZero]; ring
  have hTransfer := parity_original_historical_weighted_3d_source_ball_le_full_plus_ghost434
    s physical Wproj t H L hLw U E V Z k buf a b hSmooth hBufSupport
    T hT hWeighted
  have hProject := hProjL.2 prime l u hl hlow K k hk hkBound
    d band slot δ ξ rho xi1 xi2 xi3 signed s m mp z zp g t f T
  change (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434 s Wproj t f ζ) =
    ∑chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434 s (Wchi chi) t f ζ) at hProject
  rw [hProject] at hTransfer
  exact hTransfer
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqPsiUnrestrictedFullChiBall -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- Source-true arbitrary smooth ψ-like complex weight B633 physical
Fourier-ball inequality on the entire unrestricted original (z,m',m)
cofactor index family, without manually gated K or offdiagonal
subsets. The full Parity character projector is applied before removing
those indices and before Fourier truncation. Explicit ghost coefficient
mass, actual 3D Schwartz moment and true W1/parity/H0 remain unchanged.
The original source-to-unrestricted Sigma geometric bijection and
uniform full k,Z/branch sum remain separate debts. -/
theorem parity_eventually_original_unrestricted_actual_B633_psi_ball_le_full_chi_correlator434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L) (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (rho xi1 xi2 xi3 U E V Z : ℝ) (signed : Bool),
      0<U → 0<E → 0<V → 0<Z →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
      ∀ {ι : Type} [DecidableEq ι] (s : Finset ι)
        (m mp z zp : ι → ℕ) (g : ι → ℂ),
      (∀ i∈s, 0 < m i ∧ 0 < mp i ∧ 0 < z i ∧ 0 < zp i ∧
          (z i:ℤ)+2*k=(zp i:ℤ) ∧
        mp i∣sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (z i) ∧
        m i∣sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (zp i)) →
      ∀ (buf : ℝ → ℂ) (a b : ℝ)
        (hSmooth : ContDiff ℝ ∞ buf)
        (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
        (H : ℕ) (T : ℝ), 0<T →
      let good : ι → Prop := fun i => m i∈K ∧ mp i∈K ∧ m i≠mp i
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let A : ι → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
        L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
        (m i) (mp i) (z i) (zp i)
      let Wproj : ι → ℂ := fun i => g i*A i*alpha (m i)*star (alpha (mp i))*
        (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
         then (1:ℂ) else 0)
      let Wchi : DirichletCharacter ℂ (2*k.natAbs) → ι → ℂ := fun chi i =>
        let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0
        g i * parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha F.residual
          (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)
      let physical : ι → Prop := fun i =>
        ∃ en : ℕ, Odd en ∧ 0 < en ∧
          ∃ n : ℕ,
            n∈parityOriginalHistoricalFullNEnvelope434 V ∧
            (mp i,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
              d L band slot δ (Nat.ceil (6*U*V)) en (m i) K
              (parityOriginalHistoricalFullNEnvelope434 V) k
              (parityOriginalHistoricalActualZDyadicScale434 (z i)) ∧
            parityOriginalHistoricalCanonicalZ434 en (m i) (mp i) n=z i
      let t : ι → EuclideanSpace ℝ (Fin 3) := fun i =>
        parityOriginalHistoricalRealLogTriple434 U Z (m i) (mp i) (z i)
      let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hLw U E V Z k buf a b hSmooth hBufSupport
      ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
          parityOriginal3DPhysicalFiniteTwistedSource434
            (s.filter physical) Wproj t f ζ‖ ≤
      ‖∑chi : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs chi *
            (∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
              parityOriginal3DPhysicalFiniteTwistedSource434
                s (Wchi chi) t f ζ)‖ +
      parityOriginal3DPhysicalFiniteCoefficientMass434
        ((s.filter good).filter (fun i => ¬physical i)) Wproj *
        (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) := by
  filter_upwards [parity_eventually_original_full_chi_actual_B633_psi_ball_le_signed_correlator434
      S beta gamma Ck hS hbeta hgamma,
    parity_eventually_original_unrestricted_actual_B633_psi_full_chi_carrier_filter434
      S beta gamma Ck hS hbeta hgamma] with L hOldL hIndexL
  refine ⟨hOldL.1,?_⟩
  intro hLw prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ hDyad
    ι decι s m mp z zp g hCarrier buf a b hSmooth hBufSupport H T hT
  dsimp only
  classical
  let good : ι → Prop := fun i => m i∈K ∧ mp i∈K ∧ m i≠mp i
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let A : ι → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    (m i) (mp i) (z i) (zp i)
  let Wproj : ι → ℂ := fun i => g i*A i*alpha (m i)*star (alpha (mp i))*
    (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
     then (1:ℂ) else 0)
  let Wchi : DirichletCharacter ℂ (2*k.natAbs) → ι → ℂ := fun chi i =>
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
      (2*k.natAbs) chi 0 0
    g i * parityOriginalHistoricalB633PhysicalPairTerm434
      L rho xi1 xi2 xi3 signed alpha F.residual
      (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)
  let physical : ι → Prop := fun i =>
    ∃ en : ℕ, Odd en ∧ 0 < en ∧ ∃ n : ℕ,
      n∈parityOriginalHistoricalFullNEnvelope434 V ∧
      (mp i,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ (Nat.ceil (6*U*V)) en (m i) K
        (parityOriginalHistoricalFullNEnvelope434 V) k
        (parityOriginalHistoricalActualZDyadicScale434 (z i)) ∧
      parityOriginalHistoricalCanonicalZ434 en (m i) (mp i) n=z i
  let t : ι → EuclideanSpace ℝ (Fin 3) := fun i =>
    parityOriginalHistoricalRealLogTriple434 U Z (m i) (mp i) (z i)
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf a b hSmooth hBufSupport
  have hCarrierGood : ∀i∈s.filter good,
      0 < m i ∧ 0 < mp i ∧ 0 < z i ∧ 0 < zp i ∧
      m i∈K ∧ mp i∈K ∧ m i≠mp i ∧
      (z i:ℤ)+2*k=(zp i:ℤ) ∧
      mp i∣sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (z i) ∧
      m i∣sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (zp i) := by
    intro i hi
    have hs := (Finset.mem_filter.mp hi).1
    obtain ⟨hmK,hmpK,hNe⟩ := (Finset.mem_filter.mp hi).2
    rcases hCarrier i hs with ⟨hm,hmp,hz,hzp,hShift,hDivMp,hDivM⟩
    exact ⟨hm,hmp,hz,hzp,hmK,hmpK,hNe,hShift,hDivMp,hDivM⟩
  have hBound := hOldL.2 hLw prime l u hl hlow K k hk hkBound
    d band slot δ ξ rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ hDyad
    (s.filter good) m mp z zp g hCarrierGood
    buf a b hSmooth hBufSupport H T hT
  have hIndex := hIndexL.2 prime l u hl hlow K k hk hkBound
    d band slot δ ξ rho xi1 xi2 xi3 signed s m mp z zp g t f T
  have hPhysFilter := parity_original_actual_odd_projector_ball_carrier_filter434
    (s.filter physical) K (b629ActualFineAlpha434 prime L S gamma l u)
    k m mp (fun i => g i*A i) t f T
  have hSwap : (s.filter physical).filter good =
      (s.filter good).filter physical := by
    ext i
    simp only [Finset.mem_filter]
    tauto
  change (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434 (s.filter physical) Wproj t f ζ) =
    (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434
        ((s.filter physical).filter good) Wproj t f ζ) at hPhysFilter
  rw [hSwap] at hPhysFilter
  change (∑chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434 s (Wchi chi) t f ζ)) =
    (∑chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434
          (s.filter good) (Wchi chi) t f ζ)) at hIndex
  dsimp only at hBound
  rw [← hPhysFilter, ← hIndex] at hBound
  exact hBound
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqSigmaPositiveCarrier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 1700000

/-- The exact UNRESTRICTED Parity(4.17) Σ(z,m',m) index after
applying the genuine shifted-positive support z+2k>0. No source
e/n mask, no α-selected subset, and all P-ordinary divisors retained. -/
def parityOriginalHistoricalActualB633PositiveSigma434
    (L : ℝ) (k : ℤ) (N : Finset ℕ) :
    Finset (Σ z : ℕ, Σ mp : ℕ, ℕ) :=
  (parityOriginalHistoricalActualB633FullSigmaIndex434 L k N).filter
    (fun i => 0 < (i.1:ℤ)+2*k)

/-- Every member of the genuine unrestricted positive Sigma has
precisely the original Parity(4.16) divisor and positive endpoint
arithmetic. In particular its m' and m are positive and divide the
true P-ordinary parts of z and z+2k. No source e,n gate is smuggled
into this carrier. This establishes the exact arithmetic scope on
which the full-χ signed ψ-weighted Fourier-ball theorem applies. -/
theorem parity_original_historical_actual_positive_sigma_is_legal_cofactor434
    (L : ℝ) (k : ℤ) (N : Finset ℕ)
    (hN : ∀ z∈N, 0<z)
    (i : Σ z : ℕ, Σ mp : ℕ, ℕ)
    (hi : i∈parityOriginalHistoricalActualB633PositiveSigma434 L k N) :
    0 < i.2.2 ∧ 0 < i.2.1 ∧ 0 < i.1 ∧
    0 < (((i.1:ℤ)+2*k).toNat) ∧
    ((i.1:ℤ)+2*k)=((((i.1:ℤ)+2*k).toNat):ℤ) ∧
    i.2.1∣sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) i.1 ∧
    i.2.2∣sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L))
      (((i.1:ℤ)+2*k).toNat) := by
  classical
  obtain ⟨hmem,hshift⟩ := Finset.mem_filter.mp hi
  have hmain : i∈(N.sigma (fun z =>
    (sourceOriginalOrdinaryPart
       (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) z).divisors.sigma
      (fun _mp => (sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L))
        (((z:ℤ)+2*k).toNat)).divisors))) := hmem
  obtain ⟨hzN,hinner⟩ := Finset.mem_sigma.mp hmain
  obtain ⟨hmpD,hmD⟩ := Finset.mem_sigma.mp hinner
  have hmPos : 0 < i.2.2 := Nat.pos_of_mem_divisors hmD
  have hmpPos : 0 < i.2.1 := Nat.pos_of_mem_divisors hmpD
  have hzPos := hN i.1 hzN
  have hzpPos : 0 < (((i.1:ℤ)+2*k).toNat) := by omega
  have hCast : (i.1:ℤ)+2*k=((((i.1:ℤ)+2*k).toNat):ℤ) := by omega
  exact ⟨hmPos,hmpPos,hzPos,hzpPos,hCast,
    (Nat.mem_divisors.mp hmpD).1,(Nat.mem_divisors.mp hmD).1⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqActualSigmaPsiBall -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2650000

/-- ACTUAL unrestricted Parity(4.17) positive Sigma(z,m',m), not an
arbitrary manually gated family: original smooth dyadic ψ(z/Z)
weights and the exact full odd-e character projector are applied
to every original B633 H0/α/W1/ε cofactor pair before 3D ball
truncation. Physical B509 source e/n events are controlled by the
whole unrestricted original χ sum plus the genuine Schwartz ghost
mass/T^H. The only z hypothesis is source-positive N; it does not
assume a sharp source e/n gate or a spectral saving on a subset. -/
theorem parity_eventually_original_actual_B633_positive_sigma_psi_ball_le_full_chi434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L) (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (rho xi1 xi2 xi3 U E V Z : ℝ) (signed : Bool),
      0<U → 0<E → 0<V → 0<Z →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
      ∀ (N : Finset ℕ), (∀ z∈N,0<z) →
      ∀ (buf : ℝ → ℂ) (a b : ℝ)
        (hSmooth : ContDiff ℝ ∞ buf)
        (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
        (H : ℕ) (T : ℝ), 0<T →
      let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
      let s : Finset I := parityOriginalHistoricalActualB633PositiveSigma434 L k N
      let m : I → ℕ := fun i => i.2.2
      let mp : I → ℕ := fun i => i.2.1
      let z : I → ℕ := fun i => i.1
      let zp : I → ℕ := fun i => (((i.1:ℤ)+2*k).toNat)
      let g : I → ℂ := fun i => parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)
      let good : I → Prop := fun i => m i∈K ∧ mp i∈K ∧ m i≠mp i
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let A : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
        L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
        (m i) (mp i) (z i) (zp i)
      let Wproj : I → ℂ := fun i => g i*A i*alpha (m i)*star (alpha (mp i))*
        (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
         then (1:ℂ) else 0)
      let Wchi : DirichletCharacter ℂ (2*k.natAbs) → I → ℂ := fun chi i =>
        let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0
        g i * parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha F.residual
          (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)
      let physical : I → Prop := fun i =>
        ∃ en : ℕ, Odd en ∧ 0 < en ∧
          ∃ n : ℕ,
            n∈parityOriginalHistoricalFullNEnvelope434 V ∧
            (mp i,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
              d L band slot δ (Nat.ceil (6*U*V)) en (m i) K
              (parityOriginalHistoricalFullNEnvelope434 V) k
              (parityOriginalHistoricalActualZDyadicScale434 (z i)) ∧
            parityOriginalHistoricalCanonicalZ434 en (m i) (mp i) n=z i
      let t : I → EuclideanSpace ℝ (Fin 3) := fun i =>
        parityOriginalHistoricalRealLogTriple434 U Z (m i) (mp i) (z i)
      let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hLw U E V Z k buf a b hSmooth hBufSupport
      ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
          parityOriginal3DPhysicalFiniteTwistedSource434
            (s.filter physical) Wproj t f ζ‖ ≤
      ‖∑chi : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs chi *
            (∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
              parityOriginal3DPhysicalFiniteTwistedSource434
                s (Wchi chi) t f ζ)‖ +
      parityOriginal3DPhysicalFiniteCoefficientMass434
        ((s.filter good).filter (fun i => ¬physical i)) Wproj *
        (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) := by
  filter_upwards [parity_eventually_original_unrestricted_actual_B633_psi_ball_le_full_chi_correlator434
      S beta gamma Ck hS hbeta hgamma] with L hMain
  refine ⟨hMain.1,?_⟩
  intro hLw prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ hDyad
    N hN buf a b hSmooth hBufSupport H T hT
  dsimp only
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let s : Finset I := parityOriginalHistoricalActualB633PositiveSigma434 L k N
  let m : I → ℕ := fun i => i.2.2
  let mp : I → ℕ := fun i => i.2.1
  let z : I → ℕ := fun i => i.1
  let zp : I → ℕ := fun i => (((i.1:ℤ)+2*k).toNat)
  let g : I → ℂ := fun i => parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)
  have hCarrier : ∀ i ∈ s, 0 < m i ∧ 0 < mp i ∧ 0 < z i ∧
      0 < zp i ∧ (z i:ℤ)+2*k=(zp i:ℤ) ∧
      mp i∣sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (z i) ∧
      m i∣sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (zp i) := by
    intro i hi
    exact parity_original_historical_actual_positive_sigma_is_legal_cofactor434
      L k N hN i hi
  exact hMain.2 hLw prime l u hl hlow K k hk hkBound
    d band slot δ ξ rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ hDyad
    s m mp z zp g hCarrier buf a b hSmooth hBufSupport H T hT
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqSigmaPsiFourierExact -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- Exact FULL original Parity (4.16) double-cofactor 3D Fourier
summand as ONE complete shifted-positive dependent Σ(z,m',m) sum.
The actual smooth ψ_Z factor multiplies the literal B633 source
prime-slot residual, W1, ε, alpha and character phase; all three
original m,m',z Fourier logarithmic phases are preserved. Every
ordinary-P cofactor divisor and signed k survives, with no artificial
physical e/n subset, no Fourier error, and no hypothetical saving.
This is the missing concrete coefficient-level Sigma/Fourier Fubini
identity required BEFORE the legitimate full-χ Parity(4.17) estimate. -/
theorem parity_original_historical_actual_B633_positive_sigma_psi_fourier_exact434
    (L rho xi1 xi2 xi3 U Z : ℝ) (k : ℤ) (N : Finset ℕ)
    (alpha residual : ℕ → ℂ) (q : ℕ)
    (chi : DirichletCharacter ℂ q) (lo hi : ℕ)
    (signed : Bool) (ζ : EuclideanSpace ℝ (Fin 3)) :
    (∑i∈parityOriginalHistoricalActualB633PositiveSigma434 L k N,
      parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z) *
      parityOriginalHistoricalB633PhysicalPairTerm434
        L rho xi1 xi2 xi3 signed alpha residual q chi lo hi
        i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat) *
      parityOriginal3DPhysicalLogFourierPhase434 ζ
        (parityOriginalHistoricalRealLogTriple434 U Z i.2.2 i.2.1 i.1)) =
    parityOriginalHistoricalActualB633FullFourierCofactor434
      L rho xi1 xi2 xi3 U Z k N alpha residual q chi lo hi signed
      parityOriginalHistoricalDyadicSmoothPsi434 ζ := by
  classical
  let S := parityOriginalHistoricalActualB633FullSigmaIndex434 L k N
  let p : (Σ z : ℕ, Σ mp : ℕ, ℕ) → Prop :=
    fun i => 0 < (i.1:ℤ)+2*k
  let A : ℕ → ℕ → ℕ → ℂ := fun z mp m =>
    if 0 < (z:ℤ)+2*k then
      parityOriginalHistoricalDyadicSmoothPsi434 ((z:ℝ)/Z) *
      parityOriginalHistoricalB633PhysicalPairTerm434
        L rho xi1 xi2 xi3 signed alpha residual q chi lo hi
        m mp z (((z:ℤ)+2*k).toNat) *
      parityOriginal3DPhysicalLogFourierPhase434 ζ
        (parityOriginalHistoricalRealLogTriple434 U Z m mp z)
    else 0
  have hReindex := parity_original_historical_full_sigma_cofactor_reindex434
    L k N A
  calc
    _ = ∑i∈S, A i.1 i.2.1 i.2.2 := by
      change (∑i∈S.filter p,
        parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z) *
        parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha residual q chi lo hi
          i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat) *
        parityOriginal3DPhysicalLogFourierPhase434 ζ
          (parityOriginalHistoricalRealLogTriple434 U Z i.2.2 i.2.1 i.1)) = _
      rw [Finset.sum_filter]
    _ = ∑z∈N,
        ∑mp∈(sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) z).divisors,
        ∑m∈(sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L))
          (((z:ℤ)+2*k).toNat)).divisors,
          A z mp m := hReindex.symm
    _ = _ := by
      unfold parityOriginalHistoricalActualB633FullFourierCofactor434
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hshift : 0 < (z:ℤ)+2*k
      · simp only [hshift,ite_true]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro mp hmp
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        simp only [A,hshift,ite_true]
        ring
      · simp [A,hshift]
end Green64Analytic.Parity

end

end

