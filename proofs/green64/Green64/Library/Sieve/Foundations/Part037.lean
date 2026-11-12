module

public import Green64.Library.Sieve.Foundations.Part036
public import Green64.Library.Sieve.Foundations.Part032
public import Green64.Library.Correlation.Part070
public import Green64.Library.Sieve.Foundations.Part027
public import Green64.Library.Sieve.Foundations.Part034
public import Green64.Library.Sieve.Foundations.Part021
public import Green64.Library.Sieve.Foundations.Part031

@[expose] public section

/-!
# Sieve / Foundations / Part037

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## BPrimeActualEq417TwoGhost -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 3300000

/-- Fixed original k,Z FULL-ODD physical post-Cauchy complex Fourier
ball is bounded by the genuine unrestricted signed Parity(4.17) chi
correlation PLUS TWO source-paid Schwartz ghost moments. The source
integrand genuinely sums every odd e and all m,m',n, with no Pfree-e
gate or guessed multiplicity. The true Parity 2|k| projector is inserted
before complex norm and before Fourier truncation, and the actual
B509 H0/W1/epsilon and b629 fine alpha are kept literal. It does
NOT assert the full k/Z/fine-cell original Type II or sieve. -/
theorem parity_eventually_original_actual_Bprime_all_m_projected_ball_le_eq417_plus_two_ghost434
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
      |((2*k:ℤ):ℝ)|≤Z/128 →
      ∀ (buf : ℝ → ℂ) (a b : ℝ)
        (hSmooth : ContDiff ℝ ∞ buf)
        (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
        (H : ℕ) (T : ℝ), 0<T →
      let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
      let N : Finset ℕ := Finset.Icc 1 ⌊64*Z⌋₊
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
      let image : I → Prop := fun i =>
        parityOriginalHistoricalFullOddPsiImageAtSigma434
          d L E V Z band slot δ (Nat.ceil (6*U*V)) K k alpha i
      let t : I → EuclideanSpace ℝ (Fin 3) := fun i =>
        parityOriginalHistoricalRealLogTriple434 U Z (m i) (mp i) (z i)
      let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hLw U E V Z k buf a b hSmooth hBufSupport
      let Ssrc : ℕ → Finset (ℕ × (ℕ × ℕ)) := fun m =>
        parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
          d L E V band slot δ (Nat.ceil (6*U*V)) m K k
      let phi : ℕ → (ℕ × (ℕ × ℕ)) → I :=
        parityOriginalHistoricalUngatedSourceToSigma434
      ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
          (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
            (∑m0∈K, ∑q∈Ssrc m0,
              parityOriginalHistoricalDyadicSmoothPsi434
                ((parityOriginalHistoricalCanonicalZ434 q.1 m0 q.2.1 q.2.2:ℝ)/Z) *
              alpha m0 * star (alpha q.2.1) *
              (A (phi m0 q) *
                (if k∣((phi m0 q).2.1:ℤ)-((phi m0 q).2.2:ℤ) ∧
                  Odd (((((phi m0 q).2.1:ℤ)-((phi m0 q).2.2:ℤ))/k))
                 then (1:ℂ) else 0)) *
              parityOriginal3DPhysicalLogFourierPhase434 ζ (t (phi m0 q)))‖ ≤
      ‖∑chi : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs chi *
            (∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
              (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
              (let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
                  (2*k.natAbs) chi 0 0
               parityOriginalHistoricalActualB633FullFourierCofactor434
                 L rho xi1 xi2 xi3 U Z k N alpha F.residual
                 (2*k.natAbs) chi F.lo F.hi signed
                 parityOriginalHistoricalDyadicSmoothPsi434 ζ))‖ +
      2 * ((L^(2*parityOriginalW1PolylogExponent434)*
          ((Nat.ceil (65*Z):ℕ):ℝ)*
          (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15) *
        (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)) := by
  filter_upwards
    [parity_eventually_original_actual_B633_full_odd_source_image_psi_ball_le_eq417_plus_two_ghost434
       S beta gamma Ck hS hbeta hgamma,
     parity_actual_fine_K_restricted_rough434 S beta gamma hS hbeta hgamma]
    with L hCorr hRough
  refine ⟨hCorr.1,?_⟩
  intro hLw prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ hDyad
    hkZ buf a b hSmooth hBufSupport H T hT
  classical
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let N : Finset ℕ := Finset.Icc 1 ⌊64*Z⌋₊
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let A : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let t : I → EuclideanSpace ℝ (Fin 3) := fun i =>
    parityOriginalHistoricalRealLogTriple434 U Z i.2.2 i.2.1 i.1
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf a b hSmooth hBufSupport
  have hN : ∀z∈N, 0<z := by
    intro z hz
    exact (Finset.mem_Icc.mp hz).1
  have hOld := hCorr.2 hLw prime l u hl hlow K k hk hkBound
    d band slot δ ξ rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ
    hDyad N hN hkZ buf a b hSmooth hBufSupport H T hT
  have hActualRough (n : ℕ) (hn : alpha n≠0) :
      sourceD20Rough (Real.exp (Real.sqrt L)) n :=
    hRough prime l u hl hlow K n hn
  have hSupportAlpha (n : ℕ) (hn : alpha n≠0) : n∈K := by
    by_contra hnot
    have hz : alpha n=0 := by simp [alpha,restrictSequence,hnot]
    exact hn hz
  have hBridge :=
    parity_original_full_odd_Bprime_all_m_projected_fourier_ball_eq_source_image434
      d L E V U Z hLw hU hE hV hZ band slot δ
      (Nat.ceil (6*U*V)) K k hk alpha hActualRough hSupportAlpha A
      buf a b hSmooth hBufSupport T
  dsimp only at hOld hBridge ⊢
  -- The two terms have identical source indices and complete Schwartz
  -- Fourier kernel; only the commutative order of the five pair weights
  -- differs between their two previously checked normal forms.
  rw [hBridge]
  convert hOld using 1
end Green64Analytic.Parity

end

end

/-! ## BPrimeUnmaskedEq417TwoGhost -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 3600000

/-- The ACTUAL source all-odd physical Bprime Fourier ball itself
(with NO projected factor inserted in its original term) satisfies
unrestricted signed Parity (4.17) plus BOTH paid ghost bounds. The
projector 1 is inserted into every actual physical (e,m,m',n)
source atom by the independently native-proved whole-character
mask one, BEFORE restricting the complex sum or Fourier integral.
No false individual Dirichlet-character vanishing or signed subsum
norm monotonicity is used. Still fixed original k and dyadic Z;
global type-II k/Z/fine-cell summation is separate. -/
theorem parity_eventually_original_actual_Bprime_all_m_unmasked_ball_le_eq417_plus_two_ghost434
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
      |((2*k:ℤ):ℝ)|≤Z/128 →
      ∀ (buf : ℝ → ℂ) (a b : ℝ)
        (hSmooth : ContDiff ℝ ∞ buf)
        (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
        (H : ℕ) (T : ℝ), 0<T →
      let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
      let N : Finset ℕ := Finset.Icc 1 ⌊64*Z⌋₊
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
      let image : I → Prop := fun i =>
        parityOriginalHistoricalFullOddPsiImageAtSigma434
          d L E V Z band slot δ (Nat.ceil (6*U*V)) K k alpha i
      let t : I → EuclideanSpace ℝ (Fin 3) := fun i =>
        parityOriginalHistoricalRealLogTriple434 U Z (m i) (mp i) (z i)
      let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hLw U E V Z k buf a b hSmooth hBufSupport
      let Ssrc : ℕ → Finset (ℕ × (ℕ × ℕ)) := fun m =>
        parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
          d L E V band slot δ (Nat.ceil (6*U*V)) m K k
      let phi : ℕ → (ℕ × (ℕ × ℕ)) → I :=
        parityOriginalHistoricalUngatedSourceToSigma434
      ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
          (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
            (∑m0∈K, ∑q∈Ssrc m0,
              parityOriginalHistoricalDyadicSmoothPsi434
                ((parityOriginalHistoricalCanonicalZ434 q.1 m0 q.2.1 q.2.2:ℝ)/Z) *
              alpha m0 * star (alpha q.2.1) *
              A (phi m0 q) *
              parityOriginal3DPhysicalLogFourierPhase434 ζ (t (phi m0 q)))‖ ≤
      ‖∑chi : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs chi *
            (∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
              (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
              (let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
                  (2*k.natAbs) chi 0 0
               parityOriginalHistoricalActualB633FullFourierCofactor434
                 L rho xi1 xi2 xi3 U Z k N alpha F.residual
                 (2*k.natAbs) chi F.lo F.hi signed
                 parityOriginalHistoricalDyadicSmoothPsi434 ζ))‖ +
      2 * ((L^(2*parityOriginalW1PolylogExponent434)*
          ((Nat.ceil (65*Z):ℕ):ℝ)*
          (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15) *
        (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)) := by
  filter_upwards
    [parity_eventually_original_actual_Bprime_all_m_projected_ball_le_eq417_plus_two_ghost434
      S beta gamma Ck hS hbeta hgamma] with L hP
  refine ⟨hP.1,?_⟩
  intro hLw prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ hDyad
    hkZ buf a b hSmooth hBufSupport H T hT
  classical
  have hBound := hP.2 hLw prime l u hl hlow K k hk hkBound
    d band slot δ ξ rho xi1 xi2 xi3 U E V Z signed
    hU hE hV hZ hDyad hkZ buf a b hSmooth hBufSupport H T hT
  dsimp only at hBound ⊢
  convert hBound using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ζ
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro q hq
  have hMask := parity_original_all_m_full_odd_Bprime_source_character_mask_one434
    d L E V band slot δ (Nat.ceil (6*U*V)) m K k q hq
  -- The only difference is the already-proved whole-character
  -- projector equal to 1 at each genuine odd physical atom.
  simp only [hMask]
  ring
end Green64Analytic.Parity

end

end

/-! ## BPrimeCapfreeGhostUniform -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- The TRUE corrected cap-free Parity(4.14) lowfrequency B-prime
2-ghost Schwartz moment budget, at ALL original physical dyadic
heights Z <= 24 Cbox exp L L^(K0+88). This is stronger in actual
source RANGE than the previously checked Sigma ghost moment restricted
to Z <= 4 exp L L^(K0+88). The positive source coefficient mass
factor remains exactly the B633 unrestricted 4th-divisor bound;
no fictitious source e-, character-, or m-multiplicity is charged. -/
theorem parity_original_Bprime_capfree_full_Z_two_ghost_uniform_moment434
    (H : ℕ) (L U E V Z K0 Cbox A : ℝ) (k : ℤ)
    (hL : 8≤L) (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤U*V) (hE : E=U*L^(-K0))
    (hk : k≠0) (hZ : 0<Z)
    (hCbox : 0≤Cbox) (hLargeC : 6*Cbox≤L)
    (hZupper : Z≤24*Cbox*Real.exp L*L^(K0+88)) (hA : 0<A)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀(s:ℝ), buf s≠0 →
      -(Real.log A) ≤ s ∧ s ≤ Real.log A)
    (hLargeE : 2*A*((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L)
    (hLargeN : 8*A^2*((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
      (2:ℝ)^(H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
      ((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L)
    (R : ℝ) (hR : 1≤R)
    (hCubeR : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (T : ℝ) (hT : 0<T) :
    let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport
    let Y := Nat.ceil (65*Z)
    (L^(2*parityOriginalW1PolylogExponent434)*(Y:ℝ)*
      (1+Real.log (Y:ℝ))^15) *
      (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) ≤
    (L^(2*parityOriginalW1PolylogExponent434)*(Y:ℝ)*
      (1+Real.log (Y:ℝ))^15) *
      ((parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport H *
        L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)))/T^H) := by
  dsimp only
  have hMoment := parity_original_historical_box_source_BH_uniform_polylog434
    L U E V Z K0 Cbox A hL hK0 k hk hU hV hUV hE hZ.le
    hCbox hLargeC hZupper hA buf hSmooth hSupport H hLargeE hLargeN
    R hR hCubeR
  have hY : 1≤Nat.ceil (65*Z) := by
    exact Nat.one_le_ceil_iff.mpr (by positivity)
  have hYReal : (1:ℝ)≤((Nat.ceil (65*Z):ℕ):ℝ) := by exact_mod_cast hY
  have hLog : 0≤1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ) := by
    have hx := Real.log_nonneg hYReal
    linarith
  have hFactor : 0≤L^(2*parityOriginalW1PolylogExponent434)*
      ((Nat.ceil (65*Z):ℕ):ℝ)*
      (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15 := by
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by linarith : 0≤L) _)
        (Nat.cast_nonneg _)) (pow_nonneg hLog _)
  have hTail := div_le_div_of_nonneg_right hMoment
    (pow_nonneg hT.le H)
  exact mul_le_mul_of_nonneg_left hTail hFactor
end Green64Analytic.Parity

end

end

/-! ## BPrimeCapfreeGhostPolynomialT -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 3500000

/-- Exact real-power cancellation for positive L, with arbitrary real
precision exponent D and Fourier cutoff T=L^(X+D). -/
theorem parity_original_ghost_polynomial_T_exact_power_cancel434
    (L X D : ℝ) (hL : 0<L) : L^X/L^(X+D)=L^(-D) := by
  have hExp : L^X = L^(-D)*L^(X+D) := by
    rw [←Real.rpow_add hL]
    congr 1
    ring
  apply (div_eq_iff (ne_of_gt (Real.rpow_pos_of_pos hL (X+D)))).2
  exact hExp

/-- At the exact corrected cap-free Parity dyadic Z height, choosing
ONE polynomial Fourier cutoff T=L^(5(K0+90)(1+P+1)+D)
gives an arbitrary inverse-log saving L^-D in BOTH source-paid
ghost errors, relative to their genuine positive 4th-divisor mass
Y_F(1+log Y_F)^15 and fixed 3D moment constant. The choice
is made before L and is valid uniformly in source k,Z. The mass
factor is NOT silently bounded by x; summing source k,Z and
fine families is a separate remaining Type II integration step. -/
theorem parity_original_Bprime_capfree_ghost_polynomial_T_any_precision434
    (D : ℝ) (L U E V Z K0 Cbox A : ℝ) (k : ℤ)
    (hL : 8≤L) (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤U*V) (hE : E=U*L^(-K0))
    (hk : k≠0) (hZ : 0<Z)
    (hCbox : 0≤Cbox) (hLargeC : 6*Cbox≤L)
    (hZupper : Z≤24*Cbox*Real.exp L*L^(K0+88)) (hA : 0<A)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀(s:ℝ), buf s≠0 →
      -(Real.log A) ≤ s ∧ s ≤ Real.log A)
    (hLargeE : 2*A*((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L)
    (hLargeN : 8*A^2*((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
      (2:ℝ)^(1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
      ((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L)
    (R : ℝ) (hR : 1≤R)
    (hCubeR : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (hD : 0≤D) :
    let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport
    let Y := Nat.ceil (65*Z)
    let X : ℝ := (5*(K0+90))*(((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)
    let T : ℝ := L^(X+D)
    (L^(2*parityOriginalW1PolylogExponent434)*(Y:ℝ)*
      (1+Real.log (Y:ℝ))^15) *
      (parityOriginal3DSourceMomentFiniteBudget434 1 f/T) ≤
    (L^(2*parityOriginalW1PolylogExponent434)*(Y:ℝ)*
      (1+Real.log (Y:ℝ))^15) *
      (parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1 * L^(-D)) := by
  dsimp only
  let X : ℝ := (5*(K0+90))*
    (((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)
  let T : ℝ := L^(X+D)
  have hLp : 0<L := by linarith
  have hT : 0<T := Real.rpow_pos_of_pos hLp _
  have hSource := parity_original_Bprime_capfree_full_Z_two_ghost_uniform_moment434
    1 L U E V Z K0 Cbox A k hL hK0 hU hV hUV hE hk hZ
    hCbox hLargeC hZupper hA buf hSmooth hSupport hLargeE hLargeN
    R hR hCubeR T hT
  dsimp only at hSource
  have hPow : L^X/T=L^(-D) := by
    exact parity_original_ghost_polynomial_T_exact_power_cancel434 L X D hLp
  have hConst :
      (parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1 * L^X)/T =
      parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1 * L^(-D) := by
    rw [mul_div_assoc,hPow]
  calc
    _ ≤ (L^(2*parityOriginalW1PolylogExponent434)*((Nat.ceil (65*Z):ℕ):ℝ)*
      (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15) *
      ((parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1 * L^X)/T^1) := by
        simpa only [T,X,pow_one] using hSource
    _ = _ := by rw [pow_one,hConst]
end Green64Analytic.Parity

end

end

/-! ## BPrimeGhostMassNormalized -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 4200000

/-- Literal Parity (4.15) two-ghost positive coefficient mass normalizes
uniformly over every source dyadic Z and signed k to Z times a fixed
logarithmic power. This includes the actual ceil(65Z), not a fake
hard cutoff. The height and signed shift conditions come from the
proved original harmonic source scale budget with D=1. -/
theorem parity_eventually_original_Bprime_two_ghost_mass_normalized434
    (CZ Ck : ℝ) (hCZ : 0 ≤ CZ) :
    ∀ᶠ L : ℝ in atTop, 8 ≤ L ∧
      ∀ (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z →
        Z ≤ Real.exp L*L^CZ →
      ∀ (k : ℤ), (k.natAbs:ℝ) ≤ L^Ck →
      let Y : ℕ := Nat.ceil (65*Z)
      1 ≤ Z ∧ (Y:ℝ) ≤ 66*Z ∧
        0 ≤ 1+Real.log (Y:ℝ) ∧
        1+Real.log (Y:ℝ) ≤ L^2 ∧
        L^(2*parityOriginalW1PolylogExponent434)*(Y:ℝ)*
          (1+Real.log (Y:ℝ))^15 ≤
            66*Z*L^(2*parityOriginalW1PolylogExponent434+30) := by
  filter_upwards [parity_eventually_harmonic_scale_budget434 CZ Ck hCZ,
    eventually_ge_atTop (8:ℝ)] with L hScale hL
  refine ⟨hL,?_⟩
  intro Z hZlo hZhi k hk
  dsimp only
  have hLp : 0 < L := by linarith
  have hOneExp : (1:ℝ) ≤ Real.exp (Real.sqrt L) := by
    rw [←Real.exp_zero]
    exact Real.exp_le_exp.mpr (Real.sqrt_nonneg L)
  have hk' : |(k:ℝ)| ≤ L^Ck := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hk
  have hB := hScale.2 Z hZlo hZhi 1 (by norm_num)
    (by simpa only [Nat.cast_one] using hOneExp) k hk'
  simp only [Nat.cast_one,mul_one] at hB
  have hZ1 : 1 ≤ Z := hB.1
  have hZp : 0 < Z := by linarith
  have hYcap : ((Nat.ceil (65*Z):ℕ):ℝ) ≤ 66*Z := by
    have hCeil := Nat.ceil_lt_add_one (show 0 ≤ 65*Z by positivity)
    linarith
  have hY1 : (1:ℝ) ≤ ((Nat.ceil (65*Z):ℕ):ℝ) := by
    exact_mod_cast (Nat.one_le_ceil_iff.mpr (by positivity : 0 < 65*Z))
  have hLog0 : 0 ≤ 1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ) := by
    have hh := Real.log_nonneg hY1
    linarith
  have hLogBound : 1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ) ≤ L^2 := by
    have hh := hB.2.2
    nlinarith
  have hBase : 0 ≤ L^(2*parityOriginalW1PolylogExponent434) :=
    Real.rpow_nonneg (by linarith) _
  have hPow :
      (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15 ≤ (L^2)^15 := by
    gcongr
  have hMass :
      L^(2*parityOriginalW1PolylogExponent434)*
        ((Nat.ceil (65*Z):ℕ):ℝ)*
        (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15 ≤
      L^(2*parityOriginalW1PolylogExponent434)*(66*Z)*(L^2)^15 := by
    gcongr
  have hAlgebra :
      L^(2*parityOriginalW1PolylogExponent434)*(66*Z)*(L^2)^15 =
        66*Z*L^(2*parityOriginalW1PolylogExponent434+30) := by
    rw [←pow_mul]
    norm_num only
    rw [← Real.rpow_natCast L 30, Real.rpow_add hLp]
    ring
  exact ⟨hZ1,hYcap,hLog0,hLogBound,hMass.trans_eq hAlgebra⟩
end Green64Analytic.Parity

end

end

/-! ## BPrimeGhostMassTail -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The *actual* two-ghost source coefficient mass and 3D Fourier
moment, including ceil(65 Z) and the original five-factor Schwartz
kernel, have explicit fixed-(k,Z) inverse-log saving relative to Z.
No loss depends on the number of characters or e,n,m,m',z source
multiplicities. C_1 is the genuine fixed-buffer Schwartz constant,
which is retained rather than being silently bounded by one.
Polynomial Fourier precision D is chosen before L. -/
theorem parity_eventually_original_Bprime_two_ghost_scaled_tail434
    (CZ Ck : ℝ) (hCZ : 0≤CZ) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L) (Z : ℝ), Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ →
      ∀ k : ℤ, k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (D U E V K0 Cbox A : ℝ), 0≤D → 0≤K0 →
        0<U → 0<V → Real.exp L≤U*V → E=U*L^(-K0) →
        0≤Cbox → 6*Cbox≤L →
        Z≤24*Cbox*Real.exp L*L^(K0+88) → 0<A →
      ∀ (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
        (hSupport : ∀ (s : ℝ), buf s ≠ 0 → (-(Real.log A) ≤ s ∧ s ≤ Real.log A)),
        2*A*((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L →
        8*A^2*((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
          (2:ℝ)^(1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
          ((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L →
      ∀ R : ℝ, 1≤R →
        (∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) →
      let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hLw U E V Z k buf
          (-Real.log A) (Real.log A) hSmooth hSupport
      let Y := Nat.ceil (65*Z)
      let X : ℝ := (5*(K0+90))*
        (((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)
      let T : ℝ := L^(X+D)
      let C1 : ℝ := parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1
      (L^(2*parityOriginalW1PolylogExponent434)*(Y:ℝ)*
        (1+Real.log (Y:ℝ))^15)*
        (parityOriginal3DSourceMomentFiniteBudget434 1 f/T) ≤
      66*Z*C1*L^(2*parityOriginalW1PolylogExponent434+30-D) := by
  filter_upwards [parity_eventually_original_Bprime_two_ghost_mass_normalized434
    CZ Ck hCZ] with L hMass
  refine ⟨hMass.1,?_⟩
  intro hLw Z hZlo hZhi k hk hkBound D U E V K0 Cbox A hD hK0 hU hV hUV hE
    hCbox hLargeC hZupper hA buf hSmooth hSupport hLargeE hLargeN
    R hR hCubeR
  have hLp : 0<L := by linarith [hMass.1]
  have hZ := (hMass.2 Z hZlo hZhi k hkBound).1
  have hZp : 0<Z := by linarith
  have hPoly := parity_original_Bprime_capfree_ghost_polynomial_T_any_precision434
    D L U E V Z K0 Cbox A k hLw hK0 hU hV hUV hE hk hZp
    hCbox hLargeC hZupper hA buf hSmooth hSupport hLargeE hLargeN
    R hR hCubeR hD
  dsimp only at hPoly
  let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  have hC1 : 0≤C1 :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 1 hR
  have hDfactor : 0≤C1*L^(-D) :=
    mul_nonneg hC1 (Real.rpow_nonneg hLp.le _)
  have hBound := (hMass.2 Z hZlo hZhi k hkBound).2.2.2.2
  have hMul := mul_le_mul_of_nonneg_right hBound hDfactor
  have hPower :
      L^(2*parityOriginalW1PolylogExponent434+30)*L^(-D) =
      L^(2*parityOriginalW1PolylogExponent434+30-D) := by
    rw [←Real.rpow_add hLp]
    congr 1
  have hAlgebra :
      (66*Z*L^(2*parityOriginalW1PolylogExponent434+30))*(C1*L^(-D)) =
      66*Z*C1*L^(2*parityOriginalW1PolylogExponent434+30-D) := by
    calc
      _ = (66*Z*C1)*
          (L^(2*parityOriginalW1PolylogExponent434+30)*L^(-D)) := by ring
      _ = _ := by rw [hPower]
  exact hPoly.trans (hMul.trans_eq hAlgebra)
end Green64Analytic.Parity

end

end

/-! ## BPrimeLowfreqRhsNormalized -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Both error components of the true *integrated* low-frequency
B-prime bound (actual Parity 4.14 Fourier zero moment and both full
unrestricted B633 source ghosts) now have source-proved polynomial
budgets. This theorem only estimates the exact RHS of the previous
integrated Parity(4.17) saving; its L-independent fixed-buffer constants
are retained. The complete k/Z/fine global TypeII join is still open. -/
theorem parity_eventually_original_Bprime_integrated_lowfreq_rhs_normalized434
    (CZ Ck : ℝ) (hCZ : 0≤CZ) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L) (Z : ℝ), Real.exp L*L^(-CZ)≤Z →
        Z≤Real.exp L*L^CZ →
      ∀ k : ℤ, k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (target D U E V K0 Cbox A : ℝ), 0≤D → 0≤K0 →
        0<U → 0<V → Real.exp L≤U*V → E=U*L^(-K0) →
        0≤Cbox → 6*Cbox≤L →
        Z≤24*Cbox*Real.exp L*L^(K0+88) → 0<A →
      ∀ (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
        (hSupport : ∀ (s : ℝ), buf s ≠ 0 →
          (-(Real.log A) ≤ s ∧ s ≤ Real.log A)),
        2*A*((0+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L →
        8*A^2*((0+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
          (2:ℝ)^(0+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
          ((0+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L →
        2*A*((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L →
        8*A^2*((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
          (2:ℝ)^(1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
          ((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L →
      ∀ R : ℝ, 1≤R →
        (∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) →
      let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hLw U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport
      let Y := Nat.ceil (65*Z)
      let P := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
      let X0 : ℝ := (5*(K0+90))*(((P:ℝ)+1))
      let X1 : ℝ := (5*(K0+90))*(((1+P:ℕ):ℝ)+1)
      let T : ℝ := L^(X1+D)
      let C0 : ℝ := parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 0
      let C1 : ℝ := parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1
      (Z*L^(-target))*parityOriginal3DSourceMomentFiniteBudget434 0 f +
        2*((L^(2*parityOriginalW1PolylogExponent434)*(Y:ℝ)*
          (1+Real.log (Y:ℝ))^15)*
          (parityOriginal3DSourceMomentFiniteBudget434 1 f/T)) ≤
      (Z*L^(-target))*(C0*L^X0) +
        2*(66*Z*C1*L^(2*parityOriginalW1PolylogExponent434+30-D)) := by
  filter_upwards [parity_eventually_original_Bprime_two_ghost_scaled_tail434
    CZ Ck hCZ] with L hGhost
  refine ⟨hGhost.1,?_⟩
  intro hLw Z hZlo hZhi k hk hkBound target D U E V K0 Cbox A
    hD hK0 hU hV hUV hE hCbox hLargeC hZupper hA buf hSmooth hSupport
    hLargeE0 hLargeN0 hLargeE1 hLargeN1 R hR hCubeR
  have hLp : 0<L := by linarith [hLw]
  have hZp : 0<Z := by
    have hExp : 0<Real.exp L*L^(-CZ) :=
      mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp _)
    exact hExp.trans_le hZlo
  have hM0 := parity_original_historical_box_source_BH_uniform_polylog434
    L U E V Z K0 Cbox A hLw hK0 k hk hU hV hUV hE hZp.le
    hCbox hLargeC hZupper hA buf hSmooth hSupport
    0 hLargeE0 hLargeN0 R hR hCubeR
  have hTail := hGhost.2 hLw Z hZlo hZhi k hk hkBound
    D U E V K0 Cbox A hD hK0 hU hV hUV hE hCbox hLargeC hZupper
    hA buf hSmooth hSupport hLargeE1 hLargeN1 R hR hCubeR
  dsimp only at hM0 hTail ⊢
  have hSpectral :
      (Z*L^(-target))*parityOriginal3DSourceMomentFiniteBudget434 0
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hLw U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport) ≤
      (Z*L^(-target))*(parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 0 *
        L^((5*(K0+90))*(((0+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1))) := by
    exact mul_le_mul_of_nonneg_left hM0
      (mul_nonneg hZp.le (Real.rpow_nonneg hLp.le _))
  have hTwice := mul_le_mul_of_nonneg_left hTail (by norm_num : (0:ℝ)≤2)
  convert add_le_add hSpectral hTwice using 1 <;> simp only [Nat.zero_add]
end Green64Analytic.Parity

end

end

/-! ## BPrimeLocalPowerAbsorption -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Exact numeric parameter-budget adapter for the *actual* B-prime
Parity(4.17) 3D zero moment plus TWO source-paid ghosts. The spectral
precision target and polynomial Fourier exponent D are both selected
before L; fixed buffer constants C0,C1 are not assigned a uniform
bound over arbitrary moving smooth functions. -/
theorem parity_original_Bprime_local_power_absorption434
    (L Z goal X0 M target D C0 C1 : ℝ)
    (hL : max 1 (C0+132*C1)≤L) (hZ : 0≤Z)
    (hC0 : 0≤C0) (hC1 : 0≤C1)
    (hTarget : goal+X0+2≤target)
    (hD : goal+M+2≤D) :
    (Z*L^(-target))*(C0*L^X0) +
      2*(66*Z*C1*L^(M-D)) ≤ Z*L^(-goal) := by
  have hLone : (1:ℝ)≤L := (le_max_left _ _).trans hL
  have hLp : 0<L := by linarith
  have hCsum : C0+132*C1≤L := (le_max_right _ _).trans hL
  have hLsquare : C0+132*C1≤L^2 := by
    have hLL : L≤L^2 := by nlinarith
    linarith
  have hSpecPow : L^(-target)*L^X0≤L^(-goal-2) := by
    calc
      _ = L^(-target+X0) := by rw [Real.rpow_add hLp]
      _ ≤ L^(-goal-2) :=
        Real.rpow_le_rpow_of_exponent_le hLone (by linarith)
  have hGhostPow : L^(M-D)≤L^(-goal-2) :=
    Real.rpow_le_rpow_of_exponent_le hLone (by linarith)
  have hSpec :
      (Z*L^(-target))*(C0*L^X0)≤Z*C0*L^(-goal-2) := by
    calc
      _ = (Z*C0)*(L^(-target)*L^X0) := by ring
      _ ≤ (Z*C0)*L^(-goal-2) :=
        mul_le_mul_of_nonneg_left hSpecPow (mul_nonneg hZ hC0)
  have hGhost :
      2*(66*Z*C1*L^(M-D))≤132*Z*C1*L^(-goal-2) := by
    calc
      _ = (132*Z*C1)*L^(M-D) := by ring
      _ ≤ (132*Z*C1)*L^(-goal-2) :=
        mul_le_mul_of_nonneg_left hGhostPow (by positivity)
  have hCoeff : (C0+132*C1)*L^(-(2:ℝ))≤1 := by
    calc
      _ ≤ L^2*L^(-(2:ℝ)) :=
        mul_le_mul_of_nonneg_right hLsquare (Real.rpow_nonneg hLp.le _)
      _ = 1 := by
        rw [←Real.rpow_natCast L 2, ←Real.rpow_add hLp]
        norm_num
  calc
    _ ≤ Z*(C0+132*C1)*L^(-goal-2) := by
      convert add_le_add hSpec hGhost using 1 <;> ring
    _ = (Z*L^(-goal))*((C0+132*C1)*L^(-(2:ℝ))) := by
      rw [show -goal-2 = -goal+(-(2:ℝ)) by ring,
        Real.rpow_add hLp]
      ring
    _ ≤ (Z*L^(-goal))*1 :=
      mul_le_mul_of_nonneg_left hCoeff
        (mul_nonneg hZ (Real.rpow_nonneg hLp.le _))
    _ = _ := by ring
end Green64Analytic.Parity

end

end

/-! ## SignedFourierBallL1Transfer -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 3300000

/-! The analytic step which converts the genuinely signed, full-character
Parity(4.17) pointwise cofactor saving to a 3D Fourier-ball estimate. It
is essential that `G` is the WHOLE complex character sum at each
frequency. Applying this statement to individual physical subsums
would be invalid. Unlike an assumed Fourier L1 estimate, the RHS
uses the previously PROVED finite derivative source moment M_0(f). -/

theorem parity_original_signed_pointwise_to_ball_source_moment434
    (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ))
    (G : EuclideanSpace ℝ (Fin 3) → ℂ)
    (T M : ℝ) (hM : 0 ≤ M)
    (hInt : IntegrableOn (fun ζ : EuclideanSpace ℝ (Fin 3) =>
      (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ * G ζ)
      ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖ ≤ T} : Set _))
    (hG : ∀ ζ : EuclideanSpace ℝ (Fin 3), ‖ζ‖ ≤ T → ‖G ζ‖ ≤ M) :
    ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖ ≤ T} : Set _),
        (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ * G ζ‖ ≤
      M * parityOriginal3DSourceMomentFiniteBudget434 0 f := by
  let S : Set (EuclideanSpace ℝ (Fin 3)) := {ζ | ‖ζ‖ ≤ T}
  let F : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ) := 𝓕 f
  have hS : MeasurableSet S :=
    (isClosed_le continuous_norm continuous_const).measurableSet
  have hF : Integrable (fun ζ : EuclideanSpace ℝ (Fin 3) => F ζ) := F.integrable
  have hLeft : IntegrableOn (fun ζ : EuclideanSpace ℝ (Fin 3) =>
      ‖F ζ‖ * ‖G ζ‖) S := by
    change Integrable (fun ζ : EuclideanSpace ℝ (Fin 3) => ‖F ζ‖ * ‖G ζ‖) (volume.restrict S)
    simpa only [norm_mul, F, S] using hInt.norm
  have hRight : IntegrableOn (fun ζ : EuclideanSpace ℝ (Fin 3) =>
      M * ‖F ζ‖) S := (hF.norm.integrableOn.const_mul M)
  have hPoint : ∀ᵐ ζ ∂(volume.restrict S),
      ‖F ζ‖ * ‖G ζ‖ ≤ M * ‖F ζ‖ := by
    filter_upwards [ae_restrict_mem hS] with ζ hz
    calc
      ‖F ζ‖ * ‖G ζ‖ ≤ ‖F ζ‖ * M :=
        mul_le_mul_of_nonneg_left (hG ζ hz) (norm_nonneg _)
      _ = M * ‖F ζ‖ := mul_comm _ _
  have hMoment : (∫ ζ : EuclideanSpace ℝ (Fin 3), ‖F ζ‖) ≤
      parityOriginal3DSourceMomentFiniteBudget434 0 f := by
    simpa only [pow_zero, one_mul] using
      (parity_original_real_3d_fourier_moment_le_original_source_finite434 0 f)
  change ‖∫ ζ in S, F ζ * G ζ‖ ≤
    M * parityOriginal3DSourceMomentFiniteBudget434 0 f
  calc
    _ ≤ ∫ ζ in S, ‖F ζ * G ζ‖ := norm_integral_le_integral_norm _
    _ = ∫ ζ in S, ‖F ζ‖ * ‖G ζ‖ := by
      apply integral_congr_ae
      filter_upwards [] with ζ
      exact norm_mul _ _
    _ ≤ ∫ ζ in S, M * ‖F ζ‖ :=
      integral_mono_ae hLeft hRight hPoint
    _ = M * (∫ ζ in S, ‖F ζ‖) := integral_const_mul M _
    _ ≤ M * (∫ ζ : EuclideanSpace ℝ (Fin 3), ‖F ζ‖) :=
      mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hF.norm
          (Filter.Eventually.of_forall (fun ζ => norm_nonneg (F ζ)))) hM
    _ ≤ _ := mul_le_mul_of_nonneg_left hMoment hM

/-- No integrability assumption is needed for an ACTUAL finite smooth
Parity cofactor: its continuity, together with the uniform bound on the
Fourier ball, provides the integrability required by the signed L1
transference theorem. The full complex sum is never split by absolute
values of individual physical subsets. -/
theorem parity_original_signed_continuous_ball_source_moment434
    (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ))
    (G : EuclideanSpace ℝ (Fin 3) → ℂ)
    (T M : ℝ) (hM : 0 ≤ M)
    (hCont : Continuous G)
    (hG : ∀ ζ : EuclideanSpace ℝ (Fin 3), ‖ζ‖ ≤ T → ‖G ζ‖ ≤ M) :
    ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖ ≤ T} : Set _),
        (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ * G ζ‖ ≤
      M * parityOriginal3DSourceMomentFiniteBudget434 0 f := by
  let S : Set (EuclideanSpace ℝ (Fin 3)) := {ζ | ‖ζ‖ ≤ T}
  let F : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ) := 𝓕 f
  have hS : MeasurableSet S :=
    (isClosed_le continuous_norm continuous_const).measurableSet
  have hBase : IntegrableOn (fun ζ : EuclideanSpace ℝ (Fin 3) =>
      M * ‖F ζ‖) S := (F.integrable.norm.integrableOn.const_mul M)
  have hPoint : ∀ᵐ ζ ∂(volume.restrict S),
      ‖F ζ * G ζ‖ ≤ M * ‖F ζ‖ := by
    filter_upwards [ae_restrict_mem hS] with ζ hz
    rw [norm_mul]
    calc
      ‖F ζ‖ * ‖G ζ‖ ≤ ‖F ζ‖ * M :=
        mul_le_mul_of_nonneg_left (hG ζ hz) (norm_nonneg _)
      _ = M * ‖F ζ‖ := mul_comm _ _
  have hInt : IntegrableOn (fun ζ : EuclideanSpace ℝ (Fin 3) =>
      F ζ * G ζ) S := by
    change Integrable (fun ζ : EuclideanSpace ℝ (Fin 3) =>
      F ζ * G ζ) (volume.restrict S)
    have hBaseI : Integrable (fun ζ : EuclideanSpace ℝ (Fin 3) =>
        M * ‖F ζ‖) (volume.restrict S) := hBase
    apply hBaseI.mono (F.continuous.mul hCont).aestronglyMeasurable
    filter_upwards [hPoint] with ζ hz
    simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg hM, abs_of_nonneg (norm_nonneg (F ζ))] using hz
  exact parity_original_signed_pointwise_to_ball_source_moment434
    f G T M hM hInt hG
end Green64Analytic.Parity

end

end

/-! ## FullChiFourierContinuity -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 3800000

/-- The unrestricted source Parity B633 Fourier cofactor is continuous
in all THREE actual Fourier variables. This is proved directly from
its finite ordinary-P divisor sums and the genuine exponential
physical log phase, not a postulated measurable signed correlation. -/
theorem parity_original_actual_B633_full_fourier_cofactor_continuous434
    (L rho xi1 xi2 xi3 U Z : ℝ) (k : ℤ) (N : Finset ℕ)
    (alpha residual : ℕ → ℂ) (q : ℕ)
    (chi : DirichletCharacter ℂ q) (lo hi : ℕ)
    (signed : Bool) (psi : ℝ → ℂ) :
    Continuous (fun ζ : EuclideanSpace ℝ (Fin 3) =>
      parityOriginalHistoricalActualB633FullFourierCofactor434
        L rho xi1 xi2 xi3 U Z k N alpha residual q chi lo hi signed psi ζ) := by
  classical
  unfold parityOriginalHistoricalActualB633FullFourierCofactor434
  apply continuous_finset_sum
  intro z hz
  split_ifs with hshift
  · apply Continuous.mul continuous_const
    apply continuous_finset_sum
    intro mp hmp
    apply continuous_finset_sum
    intro m hm
    apply Continuous.mul continuous_const
    unfold parityOriginal3DPhysicalLogFourierPhase434
    fun_prop
  · exact continuous_const
end Green64Analytic.Parity

end

end

/-! ## ActualFullChiBallIntegratedSaving -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4400000

/-- TRUE signed Parity(4.17), specialized to raw b629 fine alpha and original
B509 skipped-Q core, now integrated over one entire 3D Fourier ball.
For ANY requested inverse-log precision and source reserved Q index,
J,B,S are selected before L, and the result is UNIFORM in the actual
fine support, all original bands/slots, k,Z and full Dirichlet-character
projector. On the right sits the physically constructed input's FINITE
source derivative seminorm M_0, rather than a hypothesized Fourier L1.
The shifted-frequency inequalities remain explicit and must be shown
from the polynomial cutoff in the global Type II application. -/
theorem parity_eventually_original_actual_B509_source_core_full_chi_fourier_ball_saving434
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
        ∀ (rho xi1 xi2 xi3 U : ℝ) (T : ℝ)
          (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)),
          0 < U → |rho| ≤ L^Cfreq →
          (∀ ζ : EuclideanSpace ℝ (Fin 3), ‖ζ‖ ≤ T →
            |xi1+2*Real.pi*(ζ 0)| ≤ L^Cfreq ∧
            |xi2+2*Real.pi*(ζ 1)| ≤ L^Cfreq ∧
            |xi3+2*Real.pi*(ζ 2)| ≤ L^Cfreq) →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine →
          (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (signed : Bool),
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let N := Finset.Icc 1 ⌊64*Z⌋₊
        let sourceF : DirichletCharacter ℂ (2*k.natAbs) → PrimeSlotCore := fun chi =>
          sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L)
            L band slot delta freq K alpha (2*k.natAbs) chi 0 0
        let original : EuclideanSpace ℝ (Fin 3) → ℂ := fun ζ =>
          ∑chi : DirichletCharacter ℂ (2*k.natAbs),
            parityShiftTwoMaskCoefficient434 k.natAbs chi *
              parityOriginalHistoricalActualB633FullFourierCofactor434
                L rho xi1 xi2 xi3 U Z k N alpha
                (sourceF chi).residual (2*k.natAbs) chi
                (sourceF chi).lo (sourceF chi).hi signed
                parityOriginalHistoricalDyadicSmoothPsi434 ζ
        ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖ ≤ T} : Set _),
            (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ * original ζ‖ ≤
          (Z*L^(-target))*parityOriginal3DSourceMomentFiniteBudget434 0 f := by
  obtain ⟨J,B,S,hSB,hSave⟩ :=
    parity_eventually_original_actual_B509_source_core_full_chi_fourier_saving434
      jQ target Cfreq CZ Ck beta gamma hTarget hCZ hCk hbeta hgamma
  refine ⟨J,B,S,hSB,?_⟩
  filter_upwards [hSave,eventually_ge_atTop (1:ℝ)] with L hSaveL hL
  refine ⟨hSaveL.1,hSaveL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hBand slot delta freq k hk hkBound
    rho xi1 xi2 xi3 U T f hU hrho hFrequencies
    prime lFine uFine a b hFineLow hl hu hub signed
  dsimp only
  let K := Finset.Icc a b
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let N := Finset.Icc 1 ⌊64*Z⌋₊
  let sourceF : DirichletCharacter ℂ (2*k.natAbs) → PrimeSlotCore := fun chi =>
    sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L)
      L band slot delta freq K alpha (2*k.natAbs) chi 0 0
  let G : EuclideanSpace ℝ (Fin 3) → ℂ := fun ζ =>
    ∑chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
        parityOriginalHistoricalActualB633FullFourierCofactor434
          L rho xi1 xi2 xi3 U Z k N alpha
          (sourceF chi).residual (2*k.natAbs) chi
          (sourceF chi).lo (sourceF chi).hi signed
          parityOriginalHistoricalDyadicSmoothPsi434 ζ
  have hCont : Continuous G := by
    dsimp only [G]
    apply continuous_finset_sum
    intro chi hchi
    exact continuous_const.mul
      (parity_original_actual_B633_full_fourier_cofactor_continuous434
        L rho xi1 xi2 xi3 U Z k N alpha (sourceF chi).residual
        (2*k.natAbs) chi (sourceF chi).lo (sourceF chi).hi
        signed parityOriginalHistoricalDyadicSmoothPsi434)
  have hZpos : 0 < Z := by
    have hLpos : 0 < L := by linarith
    have hh : 0 < Real.exp L*L^(-CZ) :=
      mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLpos _)
    exact hh.trans_le hZlo
  have hM : 0 ≤ Z*L^(-target) :=
    mul_nonneg hZpos.le (Real.rpow_nonneg (by linarith : 0≤L) _)
  have hPoint (ζ : EuclideanSpace ℝ (Fin 3)) (hζ : ‖ζ‖≤T) :
      ‖G ζ‖≤Z*L^(-target) := by
    obtain ⟨h1,h2,h3⟩ := hFrequencies ζ hζ
    have hSaved := hSaveL.2.2 hFamily Z hZlo hZhi band hBand slot delta freq
      k hk hkBound rho xi1 xi2 xi3 U ζ hU hrho h1 h2 h3
      prime lFine uFine a b hFineLow hl hu hub signed
    exact hSaved
  change ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖ ≤ T} : Set _),
    (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ * G ζ‖ ≤
    (Z*L^(-target))*parityOriginal3DSourceMomentFiniteBudget434 0 f
  exact parity_original_signed_continuous_ball_source_moment434
    f G T (Z*L^(-target)) hM hCont hPoint
end Green64Analytic.Parity

end

end

/-! ## FrequencyBallUniform -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 3300000

/-- Parity(4.14) shifted true 2π Fourier frequencies: if the ORIGINAL
three phase frequencies are L^C0 and the Euclidean Fourier ball is
L^Cf, ONE further exponent absorbs the sum; the complete loss is
`max C0 (Cf+1)+1`, with all exponents fixed BEFORE choosing L. -/
theorem parity_original_real_3d_shifted_frequency_polynomial_ball434
    (L C0 Cf xi : ℝ) (hL : 8≤L)
    (ζ : EuclideanSpace ℝ (Fin 3)) (i : Fin 3)
    (hxi : |xi|≤L^C0) (hζ : ‖ζ‖≤L^Cf) :
    |xi+2*Real.pi*(ζ i)|≤L^(max C0 (Cf+1)+1) := by
  have hLp : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  let M : ℝ := max C0 (Cf+1)
  have hM0 : 0≤L^M := Real.rpow_nonneg hLp.le _
  have hXm : L^C0≤L^M :=
    Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _)
  have hFm : L^(Cf+1)≤L^M :=
    Real.rpow_le_rpow_of_exponent_le hL1 (le_max_right _ _)
  have hShift := parity_original_real_3d_fourier_frequency_budget434 L Cf hL ζ hζ i
  change |xi+2*Real.pi*(ζ i)|≤L^(M+1)
  calc
    _ ≤ |xi|+|2*Real.pi*(ζ i)| := abs_add_le _ _
    _ ≤ 2*L^M := by linarith
    _ ≤ L*L^M := mul_le_mul_of_nonneg_right (by linarith : 2≤L) hM0
    _ = L^(M+1) := by rw [Real.rpow_add hLp, Real.rpow_one]; ring

/-- EXACT three-coordinate uniform source frequency range on the
entire REAL Euclidean Fourier ball, not three unrelated cutoffs. -/
theorem parity_original_real_3d_all_shifted_poly_ball434
    (L C0 Cf xi1 xi2 xi3 T : ℝ) (hL : 8≤L)
    (hT : T≤L^Cf)
    (hxi1 : |xi1|≤L^C0) (hxi2 : |xi2|≤L^C0)
    (hxi3 : |xi3|≤L^C0)
    (ζ : EuclideanSpace ℝ (Fin 3)) (hζ : ‖ζ‖≤T) :
    |xi1+2*Real.pi*(ζ 0)|≤L^(max C0 (Cf+1)+1) ∧
    |xi2+2*Real.pi*(ζ 1)|≤L^(max C0 (Cf+1)+1) ∧
    |xi3+2*Real.pi*(ζ 2)|≤L^(max C0 (Cf+1)+1) := by
  have hζp : ‖ζ‖≤L^Cf := hζ.trans hT
  exact ⟨parity_original_real_3d_shifted_frequency_polynomial_ball434
    L C0 Cf xi1 hL ζ 0 hxi1 hζp,
    parity_original_real_3d_shifted_frequency_polynomial_ball434
    L C0 Cf xi2 hL ζ 1 hxi2 hζp,
    parity_original_real_3d_shifted_frequency_polynomial_ball434
    L C0 Cf xi3 hL ζ 2 hxi3 hζp⟩
end Green64Analytic.Parity

end

end

/-! ## ActualFullChiPolynomialBallSaving -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4400000

/-- Entire original full-character signed Parity(4.17) correlation is
bounded AFTER real 3D Fourier integration with no assumed shifted
frequency range. The ORIGINAL three phase frequencies and rho have
budget L^C0, the Fourier ball has T<=L^Cf, and the exact 2π factor
is absorbed by Cfreq=max C0 (Cf+1)+1 BEFORE the choice of J,B,S,L.
This is uniform in original k,Z,Q,slot and any actual b629 fine cell.
The output retains M_0(f): the true finite Schwartz source moment.
There is no false complex subset monotonicity or #character loss. -/
theorem parity_eventually_original_actual_B509_full_chi_polynomial_ball_saving434
    (jQ : ℕ) (target C0 Cf CZ Ck beta gamma : ℝ)
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
        ∀ (rho xi1 xi2 xi3 U T : ℝ)
          (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)),
          0 < U → T ≤ L^Cf →
          |rho| ≤ L^C0 → |xi1| ≤ L^C0 →
          |xi2| ≤ L^C0 → |xi3| ≤ L^C0 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine →
          (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (signed : Bool),
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let N := Finset.Icc 1 ⌊64*Z⌋₊
        let sourceF : DirichletCharacter ℂ (2*k.natAbs) → PrimeSlotCore := fun chi =>
          sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L)
            L band slot delta freq K alpha (2*k.natAbs) chi 0 0
        let original : EuclideanSpace ℝ (Fin 3) → ℂ := fun ζ =>
          ∑chi : DirichletCharacter ℂ (2*k.natAbs),
            parityShiftTwoMaskCoefficient434 k.natAbs chi *
              parityOriginalHistoricalActualB633FullFourierCofactor434
                L rho xi1 xi2 xi3 U Z k N alpha
                (sourceF chi).residual (2*k.natAbs) chi
                (sourceF chi).lo (sourceF chi).hi signed
                parityOriginalHistoricalDyadicSmoothPsi434 ζ
        ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖ ≤ T} : Set _),
            (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ * original ζ‖ ≤
          (Z*L^(-target))*parityOriginal3DSourceMomentFiniteBudget434 0 f := by
  let Cfreq : ℝ := max C0 (Cf+1)+1
  obtain ⟨J,B,S,hSB,hSave⟩ :=
    parity_eventually_original_actual_B509_source_core_full_chi_fourier_ball_saving434
      jQ target Cfreq CZ Ck beta gamma hTarget hCZ hCk hbeta hgamma
  refine ⟨J,B,S,hSB,?_⟩
  filter_upwards [hSave,eventually_ge_atTop (8:ℝ)] with L hSaveL hL
  refine ⟨hSaveL.1,hSaveL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hBand slot delta freq k hk hkBound
    rho xi1 xi2 xi3 U T f hU hT hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu hub signed
  dsimp only
  have hRho : |rho|≤L^Cfreq := by
    have he : C0 ≤ Cfreq := by dsimp [Cfreq]; linarith [le_max_left C0 (Cf+1)]
    exact hrho.trans (Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤L) he)
  have hFrequencies (ζ : EuclideanSpace ℝ (Fin 3)) (hζ : ‖ζ‖≤T) :
      |xi1+2*Real.pi*(ζ 0)|≤L^Cfreq ∧
      |xi2+2*Real.pi*(ζ 1)|≤L^Cfreq ∧
      |xi3+2*Real.pi*(ζ 2)|≤L^Cfreq := by
    exact parity_original_real_3d_all_shifted_poly_ball434
      L C0 Cf xi1 xi2 xi3 T hL hT hxi1 hxi2 hxi3 ζ hζ
  exact hSaveL.2.2 hFamily Z hZlo hZhi band hBand slot delta freq
    k hk hkBound rho xi1 xi2 xi3 U T f hU hRho hFrequencies
    prime lFine uFine a b hFineLow hl hu hub signed
end Green64Analytic.Parity

end

end

/-! ## FullChiFourierFubini -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 3400000

/-- REAL Fourier ball, arbitrary finite characters, complex signed
coefficients. The finite character projector is moved UNDER the same
3D Fourier integral without absolute-value or #character cost.
Integrability is verified from the continuous true Fourier cofactor
and actual compact Euclidean ball; no swap of a divergent series. -/
theorem parity_original_full_character_fourier_ball_fubini434
    {ι : Type*} [Fintype ι]
    (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) (T : ℝ)
    (c : ι → ℂ) (H : ι → EuclideanSpace ℝ (Fin 3) → ℂ)
    (hContinuous : ∀ i, Continuous (H i)) :
    (∑i : ι, c i *
      (∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖ ≤ T} : Set _),
        (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ * H i ζ)) =
    ∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖ ≤ T} : Set _),
      (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
        (∑i : ι, c i * H i ζ) := by
  classical
  let S : Set (EuclideanSpace ℝ (Fin 3)) := {ζ | ‖ζ‖ ≤ T}
  let F : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ) := 𝓕 f
  have hEq : S=Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) T := by
    ext ζ
    simp [S, Metric.mem_closedBall, dist_zero_right]
  have hCompact : IsCompact S := by
    rw [hEq]
    exact isCompact_closedBall _ _
  have hIntegrable (i : ι) : IntegrableOn (fun ζ : EuclideanSpace ℝ (Fin 3) =>
      c i * (F ζ * H i ζ)) S := by
    have hC : Continuous (fun ζ : EuclideanSpace ℝ (Fin 3) =>
        c i * (F ζ * H i ζ)) :=
      continuous_const.mul (F.continuous.mul (hContinuous i))
    exact hC.continuousOn.integrableOn_compact hCompact
  change (∑i : ι, c i * (∫ ζ in S, F ζ * H i ζ)) =
      ∫ ζ in S, F ζ * (∑i : ι, c i * H i ζ)
  calc
    _ = ∑i : ι, (∫ ζ in S, c i * (F ζ * H i ζ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul]
    _ = ∫ ζ in S, ∑i : ι, c i * (F ζ * H i ζ) := by
      rw [integral_finset_sum]
      intro i hi
      exact hIntegrable i
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ζ
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
end Green64Analytic.Parity

end

end

/-! ## BPrimeIntegratedEq417Saving -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4900000

/-- Source-exact original full-odd B' post-Cauchy complex low-frequency
ball has now been bounded by an *integrated* unrestricted signed
Parity(4.17) saving, plus TWO distinct source-paid ghosts. In particular
this is no longer a mere norm bound by another unestimated χ-integral.
At every fixed original k,Z,Q,band,slot and actual b629 fine interval,
for ANY requested target, Parity J,B,S are chosen first. The same B509
actual e,n,m,m',z source coefficients and α,ψ,H0,W1 and epsilon
appear literally in the left side. No Pfree-e gate. We use Ybox=ceil6UV.

The remaining full original TypeII(4.2) obligations are: effective
source M0 and MH bounds with the proper global polynomial Fourier T,
positive mass #k/Z/branch/fine sums and high-frequency Fourier tail.
This statement does NOT say original global TypeII has been proved. -/
theorem parity_eventually_original_actual_Bprime_full_odd_lowfreq_le_integrated_417_plus_two_ghost434
    (jQ : ℕ) (target C0 Cf CZ Ck beta gamma : ℝ)
    (hTarget : 0 < target) (hCZ : 0≤CZ) (hCk : 0≤Ck)
    (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, 8≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hLw : 8≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
        ∀ (rho xi1 xi2 xi3 U E V T : ℝ) (signed : Bool),
          0<U → 0<E → 0<V → 0<T → T≤L^Cf →
          |rho|≤L^C0 → |xi1|≤L^C0 →
          |xi2|≤L^C0 → |xi3|≤L^C0 →
          |((2*k:ℤ):ℝ)|≤Z/128 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L)≤(lFine:ℝ) →
          2≤lFine → uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
        ∀ (buf : ℝ → ℂ) (smoothLo smoothHi : ℝ)
          (hSmooth : ContDiff ℝ ∞ buf)
          (hBufSupport : ∀x:ℝ,buf x≠0 → smoothLo ≤ x ∧ x ≤ smoothHi)
          (H : ℕ),
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let d := sourceOriginalLiteralDepth 20 L
        let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
        let N : Finset ℕ := Finset.Icc 1 ⌊64*Z⌋₊
        let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
          (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
        let A : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
          L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
          i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
        let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hLw U E V Z k buf smoothLo smoothHi hSmooth hBufSupport
        let sourceTerms : ℕ → Finset (ℕ × (ℕ × ℕ)) := fun m =>
          parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
            d L E V band slot delta (Nat.ceil (6*U*V)) m K k
        let phi : ℕ → (ℕ × (ℕ × ℕ)) → I :=
          parityOriginalHistoricalUngatedSourceToSigma434
        ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
            (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
              (∑m0∈K, ∑q∈sourceTerms m0,
                parityOriginalHistoricalDyadicSmoothPsi434
                  ((parityOriginalHistoricalCanonicalZ434 q.1 m0 q.2.1 q.2.2:ℝ)/Z) *
                alpha m0 * star (alpha q.2.1) *
                A (phi m0 q) *
                parityOriginal3DPhysicalLogFourierPhase434 ζ
                  (parityOriginalHistoricalRealLogTriple434 U Z
                    (phi m0 q).2.2 (phi m0 q).2.1 (phi m0 q).1))‖ ≤
        (Z*L^(-target))*parityOriginal3DSourceMomentFiniteBudget434 0 f +
          2*((L^(2*parityOriginalW1PolylogExponent434)*
            ((Nat.ceil (65*Z):ℕ):ℝ)*
            (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15)*
          (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)) := by
  obtain ⟨J,B,S,hSB,hFourier⟩ :=
    parity_eventually_original_actual_B509_full_chi_polynomial_ball_saving434
      jQ target C0 Cf CZ Ck beta gamma hTarget hCZ hCk hbeta hgamma
  have hS : 0<S := by
    have hb : 0≤(B:ℝ) := Nat.cast_nonneg B
    linarith
  have hSource :=
    parity_eventually_original_actual_Bprime_all_m_unmasked_ball_le_eq417_plus_two_ghost434
      S beta gamma Ck hS hbeta hgamma
  refine ⟨J,B,S,hSB,?_⟩
  filter_upwards [hFourier,hSource,eventually_ge_atTop (8:ℝ)]
    with L hFourierL hSourceL hL
  refine ⟨hL,hFourierL.1,hFourierL.2.1,?_⟩
  intro hLw hFamily Z hZlo hZhi band hBand slot delta freq k hk hkBound
    rho xi1 xi2 xi3 U E V T signed hU hE hV hT hTCut
    hrho hxi1 hxi2 hxi3 hkZ
    prime lFine uFine a b hFineLow hl hu hub hDyad
    buf smoothLo smoothHi hSmooth hBufSupport H
  classical
  let K := Finset.Icc a b
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let d := sourceOriginalLiteralDepth 20 L
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let N : Finset ℕ := Finset.Icc 1 ⌊64*Z⌋₊
  let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let A : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf smoothLo smoothHi hSmooth hBufSupport
  let sourceTerms : ℕ → Finset (ℕ × (ℕ × ℕ)) := fun m =>
    parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot delta (Nat.ceil (6*U*V)) m K k
  let phi : ℕ → (ℕ × (ℕ × ℕ)) → I :=
    parityOriginalHistoricalUngatedSourceToSigma434
  have hZ : 0<Z := by
    have hLp : 0<L := by linarith
    have hh : 0<Real.exp L*L^(-CZ) :=
      mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp _)
    exact hh.trans_le hZlo
  have hB := hSourceL.2 hLw prime lFine uFine hl hFineLow K k hk hkBound
    d band slot delta freq rho xi1 xi2 xi3 U E V Z signed
    hU hE hV hZ hDyad hkZ
    buf smoothLo smoothHi hSmooth hBufSupport H T hT
  have hSave := hFourierL.2.2 hFamily Z hZlo hZhi band hBand slot delta freq
    k hk hkBound rho xi1 xi2 xi3 U T f hU hTCut hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu hub signed
  let Fχ : DirichletCharacter ℂ (2*k.natAbs) → PrimeSlotCore := fun chi =>
    sourceNativePrimeCore 20 d L band slot delta freq K alpha
      (2*k.natAbs) chi 0 0
  let Hχ : DirichletCharacter ℂ (2*k.natAbs) →
      EuclideanSpace ℝ (Fin 3) → ℂ := fun chi ζ =>
    parityOriginalHistoricalActualB633FullFourierCofactor434
      L rho xi1 xi2 xi3 U Z k N alpha (Fχ chi).residual
      (2*k.natAbs) chi (Fχ chi).lo (Fχ chi).hi signed
      parityOriginalHistoricalDyadicSmoothPsi434 ζ
  let c : DirichletCharacter ℂ (2*k.natAbs) → ℂ :=
    fun chi => parityShiftTwoMaskCoefficient434 k.natAbs chi
  have hCont (chi : DirichletCharacter ℂ (2*k.natAbs)) : Continuous (Hχ chi) :=
    parity_original_actual_B633_full_fourier_cofactor_continuous434
      L rho xi1 xi2 xi3 U Z k N alpha (Fχ chi).residual
      (2*k.natAbs) chi (Fχ chi).lo (Fχ chi).hi signed
      parityOriginalHistoricalDyadicSmoothPsi434
  have hSwap := parity_original_full_character_fourier_ball_fubini434
    f T c Hχ hCont
  -- Both inequalities are defined on precisely the same raw K,
  -- sorted source core and complete unrestricted 2|k| character family.
  -- In particular the ghosts are retained at exactly their old source mass.
  dsimp only at hB hSave hSwap ⊢
  calc
    _ ≤ ‖∑chi : DirichletCharacter ℂ (2*k.natAbs),
          c chi * (∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
            (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ * Hχ chi ζ)‖ +
        2*((L^(2*parityOriginalW1PolylogExponent434)*
            ((Nat.ceil (65*Z):ℕ):ℝ)*
            (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15)*
          (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)) := by
            convert hB using 1
    _ = ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
          (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
            (∑chi : DirichletCharacter ℂ (2*k.natAbs),
              c chi * Hχ chi ζ)‖ +
        2*((L^(2*parityOriginalW1PolylogExponent434)*
            ((Nat.ceil (65*Z):ℕ):ℝ)*
            (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15)*
          (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)) := by
            rw [hSwap]
    _ ≤ (Z*L^(-target))*parityOriginal3DSourceMomentFiniteBudget434 0 f +
        2*((L^(2*parityOriginalW1PolylogExponent434)*
            ((Nat.ceil (65*Z):ℕ):ℝ)*
            (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15)*
          (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)) := by
            exact add_le_add_left hSave _
end Green64Analytic.Parity

end

end

/-! ## BPrimeFixedKZAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Fully integrated ORIGINAL, SOURCE-correct, fixed-(k,Z) B-prime
post-Cauchy lowfrequency Fourier-ball saving. This uses a single
polynomial Fourier cutoff chosen before L, the true Parity (4.14)
zero- and first-order Schwartz moments, both independently paid
B633 ghosts, and the actual specialized signed Parity(4.17) estimate.
All source e,n,m,m',z coefficients and full characters stay present.
No theorem about the full k/Z/fine-cell original Type II sum is claimed. -/
theorem parity_eventually_original_actual_Bprime_fixed_kZ_lowfreq_any_log434
    (jQ : ℕ) (goal target Cfreq Cf CZ Ck beta gamma K0 Cbox A R D : ℝ)
    (buf : ℝ → ℂ)
    (hGoal : 0≤goal) (hTargetPos : 0<target)
    (hCZ : 0≤CZ) (hCk : 0≤Ck)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 0≤Cbox) (hA : 0<A) (hR : 1≤R)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀ (s : ℝ), buf s ≠ 0 → (-(Real.log A) ≤ s ∧ s ≤ Real.log A))
    (hCubeR : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A, ‖t‖≤R)
    (hD : 0≤D)
    (hTarget : goal+(5*(K0+90))*
       (((volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℝ)+1)+2≤target)
    (hDprecision : goal+(2*parityOriginalW1PolylogExponent434+30)+2≤D)
    (hCf : (5*(K0+90))*
      (((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)+D≤Cf) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, 8≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hLw : 8≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
        ∀ (rho xi1 xi2 xi3 U E V : ℝ) (signed : Bool),
          0<U → 0<E → 0<V →
          Real.exp L≤U*V → E=U*L^(-K0) →
          Z≤24*Cbox*Real.exp L*L^(K0+88) →
          |rho|≤L^Cfreq → |xi1|≤L^Cfreq →
          |xi2|≤L^Cfreq → |xi3|≤L^Cfreq →
          |((2*k:ℤ):ℝ)|≤Z/128 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L)≤(lFine:ℝ) →
          2≤lFine → uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let d := sourceOriginalLiteralDepth 20 L
        let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
        let N : Finset ℕ := Finset.Icc 1 ⌊64*Z⌋₊
        let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
          (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
        let Atom : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
          L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
          i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
        let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hLw U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport
        let P := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
        let X1 : ℝ := (5*(K0+90))*(((1+P:ℕ):ℝ)+1)
        let T : ℝ := L^(X1+D)
        let sourceTerms : ℕ → Finset (ℕ × (ℕ × ℕ)) := fun m =>
          parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
            d L E V band slot delta (Nat.ceil (6*U*V)) m K k
        let phi : ℕ → (ℕ × (ℕ × ℕ)) → I :=
          parityOriginalHistoricalUngatedSourceToSigma434
        ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
            (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
              (∑m0∈K, ∑q∈sourceTerms m0,
                parityOriginalHistoricalDyadicSmoothPsi434
                  ((parityOriginalHistoricalCanonicalZ434 q.1 m0 q.2.1 q.2.2:ℝ)/Z) *
                alpha m0 * star (alpha q.2.1) *
                Atom (phi m0 q) *
                parityOriginal3DPhysicalLogFourierPhase434 ζ
                  (parityOriginalHistoricalRealLogTriple434 U Z
                    (phi m0 q).2.2 (phi m0 q).2.1 (phi m0 q).1))‖ ≤
          Z*L^(-goal) := by
  obtain ⟨J,B,S,hSB,hIntegrated⟩ :=
    parity_eventually_original_actual_Bprime_full_odd_lowfreq_le_integrated_417_plus_two_ghost434
      jQ target Cfreq Cf CZ Ck beta gamma hTargetPos hCZ hCk hbeta hgamma
  have hNumeric := parity_eventually_original_Bprime_integrated_lowfreq_rhs_normalized434
    CZ Ck hCZ
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let X0 : ℝ := (5*(K0+90))*((P:ℝ)+1)
  let X1 : ℝ := (5*(K0+90))*(((1+P:ℕ):ℝ)+1)
  let M : ℝ := 2*parityOriginalW1PolylogExponent434+30
  let Czero : ℝ := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cone : ℝ := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let E0 : ℝ := 2*A*((0+P).factorial:ℝ)
  let N0 : ℝ := 8*A^2*((0+P).factorial:ℝ)*(2:ℝ)^(0+P)+((0+P).factorial:ℝ)*A
  let E1 : ℝ := 2*A*((1+P).factorial:ℝ)
  let N1 : ℝ := 8*A^2*((1+P).factorial:ℝ)*(2:ℝ)^(1+P)+((1+P).factorial:ℝ)*A
  have hCzero : 0≤Czero :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 0 hR
  have hCone : 0≤Cone :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 1 hR
  refine ⟨J,B,S,hSB,?_⟩
  filter_upwards [hIntegrated,hNumeric,
    eventually_ge_atTop (6*Cbox),
    eventually_ge_atTop (max 1 (Czero+132*Cone)),
    eventually_ge_atTop E0,eventually_ge_atTop N0,
    eventually_ge_atTop E1,eventually_ge_atTop N1]
    with L hIntegratedL hNumericL hLargeC hLargeConst hLargeE0 hLargeN0 hLargeE1 hLargeN1
  refine ⟨hIntegratedL.1,hIntegratedL.2.1,hIntegratedL.2.2.1,?_⟩
  intro hLw hFamily Z hZlo hZhi band hBand slot delta freq k hk hkBound
    rho xi1 xi2 xi3 U E V signed hU hE hV hUV hEscale hZupper
    hrho hxi1 hxi2 hxi3 hkZ
    prime lFine uFine a b hFineLow hl hu hub hDyad
  classical
  let T : ℝ := L^(X1+D)
  have hLp : 0<L := by linarith [hLw]
  have hLone : (1:ℝ)≤L := by linarith [hLw]
  have hT : 0<T := Real.rpow_pos_of_pos hLp _
  have hTCut : T≤L^Cf := Real.rpow_le_rpow_of_exponent_le hLone hCf
  have hFirst := hIntegratedL.2.2.2 hLw hFamily Z hZlo hZhi
    band hBand slot delta freq k hk hkBound
    rho xi1 xi2 xi3 U E V T signed hU hE hV hT hTCut
    hrho hxi1 hxi2 hxi3 hkZ
    prime lFine uFine a b hFineLow hl hu hub hDyad
    buf (-Real.log A) (Real.log A) hSmooth hSupport 1
  have hRHS := hNumericL.2 hLw Z hZlo hZhi k hk hkBound
    target D U E V K0 Cbox A hD hK0 hU hV hUV hEscale hCbox hLargeC
    hZupper hA buf hSmooth hSupport
    hLargeE0 hLargeN0 hLargeE1 hLargeN1 R hR hCubeR
  have hZp : 0<Z := by
    have hh : 0<Real.exp L*L^(-CZ) :=
      mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp _)
    exact hh.trans_le hZlo
  have hAbsorb := parity_original_Bprime_local_power_absorption434
    L Z goal X0 M target D Czero Cone hLargeConst hZp.le
    hCzero hCone hTarget hDprecision
  dsimp only at hFirst hRHS ⊢
  calc
    _ ≤ (Z*L^(-target))*
        parityOriginal3DSourceMomentFiniteBudget434 0
          (parityOriginalHistoricalActualDyadicCutoffSchwartz434
            L hLw U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport) +
          2*((L^(2*parityOriginalW1PolylogExponent434)*
            ((Nat.ceil (65*Z):ℕ):ℝ)*
            (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15)*
            (parityOriginal3DSourceMomentFiniteBudget434 1
              (parityOriginalHistoricalActualDyadicCutoffSchwartz434
                L hLw U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport)/T)) := by
        simpa only [pow_one] using hFirst
    _ ≤ (Z*L^(-target))*(Czero*L^X0)+
        2*(66*Z*Cone*L^(M-D)) := by
        convert hRHS using 1
    _ ≤ Z*L^(-goal) := by exact hAbsorb
end Green64Analytic.Parity

end

end

/-! ## BPrimePrimaryM0Normalization -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 3600000

/-- The REAL original cap-free Parity(4.14) smooth kernel is quantitatively
L1 in Fourier at H=0. This is source-derived from all 5 smooth
factors on the actual Ybox=ceil(6UV) physical z height, not an
independent Fourier-boundedness hypothesis. It is exactly the M0
needed in the new integrated Bprime -> signed Eq(4.17) theorem. -/
theorem parity_original_actual_capfree_Bprime_M0_uniform_polylog434
    (L U E V Z K0 Cbox A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hCbox : 0≤Cbox) (hLargeC : 6*Cbox≤L)
    (hZupper : Z≤24*Cbox*Real.exp L*L^(K0+88))
    (hA : 0<A) (buf : ℝ → ℂ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ s : ℝ, buf s ≠ 0 →
      -Real.log A ≤ s ∧ s ≤ Real.log A)
    (hLargeE : 2*A*((0+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L)
    (hLargeN : 8*A^2*((0+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
      (2:ℝ)^(0+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
      ((0+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L)
    (R : ℝ) (hR : 1≤R)
    (hCubeR : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    parityOriginal3DSourceMomentFiniteBudget434 0
      (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf (-Real.log A) (Real.log A)
        hBufSmooth hBufSupport) ≤
    parityOriginalHistoricalActual3DFourierMomentFixedK434
      A R buf hBufSmooth hBufSupport 0 *
      L^((5*(K0+90))*((((volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) := by
  simpa only [Nat.zero_add] using
    (parity_original_historical_box_source_BH_uniform_polylog434
      L U E V Z K0 Cbox A hL hK0 k hk hU hV hUV hE hZ
      hCbox hLargeC hZupper hA buf hBufSmooth hBufSupport 0
      hLargeE hLargeN R hR hCubeR)

/-- One arbitrarily deep extra input spectral precision exactly pays
for the true M0(f) exponent, independently of k,Z,ζ and fine cells.
No hidden selection of J/B/S after L: the exponent is fixed by K0
and the literal Euclidean 3D `integrablePower`. -/
theorem parity_original_actual_capfree_Bprime_primary_inverse_log_from_M0434
    (L Z D K0 Cmoment M0 : ℝ)
    (hL : 8≤L) (hZ : 0≤Z)
    (hM0 : M0≤Cmoment*
      L^((5*(K0+90))*((((volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1))) :
    (Z*L^(-(D+(5*(K0+90))*((((volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1))))*M0 ≤
    Cmoment*Z*L^(-D) := by
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let p0 : ℝ := (5*(K0+90))*((P:ℝ)+1)
  have hLp : 0<L := by linarith
  have hMul : 0≤Z*L^(-(D+p0)) :=
    mul_nonneg hZ (Real.rpow_nonneg hLp.le _)
  have hPow : L^(-(D+p0))*L^p0=L^(-D) := by
    rw [←Real.rpow_add hLp]
    congr 1
    ring
  change (Z*L^(-(D+p0)))*M0 ≤ Cmoment*Z*L^(-D)
  calc
    _ ≤ (Z*L^(-(D+p0)))*(Cmoment*L^p0) :=
      mul_le_mul_of_nonneg_left hM0 hMul
    _ = Cmoment*Z*(L^(-(D+p0))*L^p0) := by ring
    _ = _ := by rw [hPow]
end Green64Analytic.Parity

end

end

/-! ## ActualB509PrimaryM0IntegratedSaving -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4900000

/-- THE REAL original Parity(4.14) Schwartz kernel and TRUE unrestricted
signed Eq4.17 correlation, now jointly yielding a fixed k,Z bound
of `C_0 Z L^-D` after the 3D Fourier integral. The original
Schwartz M0 is not a hypothetical L1 Fourier constant; it was
proved from source eta_e/n on the capfree Ybox geometry.

For a requested D and fixed original K0, define source precision
`target=D+5(K0+90)(P+1)` BEFORE selecting Parity J,B,S and L.
For each actual fine b629 cell and original reserved Q/slot, every
source k,Z and all Fourier frequencies are covered. Original ghost
errors are separate, still due in the Bprime -> unrestricted transfer.
This theorem is NOT global TypeII (4.2). -/
theorem parity_eventually_original_actual_B509_full_chi_ball_source_M0_inverse_log434
    (jQ : ℕ) (D C0 Cf CZ Ck beta gamma K0 Cbox A R : ℝ)
    (hD : 0 < D) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck)
    (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hK0 : 0 ≤ K0) (hCbox : 1 ≤ Cbox)
    (hA : 0 < A) (hR : 1 ≤ R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ, buf t ≠ 0 → -Real.log A ≤ t ∧ t ≤ Real.log A)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A, ‖t‖ ≤ R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, 8≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hLw : 8≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (rho xi1 xi2 xi3 U E V T : ℝ),
          0 < U → 0 < V → Real.exp L ≤ U*V →
          E = U*L^(-K0) →
          Z ≤ 24*Cbox*Real.exp L*L^(K0+88) →
          T ≤ L^Cf →
          |rho| ≤ L^C0 → |xi1| ≤ L^C0 →
          |xi2| ≤ L^C0 → |xi3| ≤ L^C0 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine →
          (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (signed : Bool),
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let N := Finset.Icc 1 ⌊64*Z⌋₊
        let sourceF : DirichletCharacter ℂ (2*k.natAbs) → PrimeSlotCore := fun chi =>
          sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L)
            L band slot delta freq K alpha (2*k.natAbs) chi 0 0
        let original : EuclideanSpace ℝ (Fin 3) → ℂ := fun ζ =>
          ∑chi : DirichletCharacter ℂ (2*k.natAbs),
            parityShiftTwoMaskCoefficient434 k.natAbs chi *
              parityOriginalHistoricalActualB633FullFourierCofactor434
                L rho xi1 xi2 xi3 U Z k N alpha
                (sourceF chi).residual (2*k.natAbs) chi
                (sourceF chi).lo (sourceF chi).hi signed
                parityOriginalHistoricalDyadicSmoothPsi434 ζ
        let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hLw U E V Z k buf (-Real.log A) (Real.log A)
          hSmooth hSupport
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖ ≤ T} : Set _),
            (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ * original ζ‖ ≤
          Cmoment*Z*L^(-D) := by
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let p0 : ℝ := 5*(K0+90)*((P:ℝ)+1)
  have hp0 : 0≤p0 := by
    have hK : 0≤K0+90 := by linarith
    have hp : 0≤(P:ℝ) := Nat.cast_nonneg _
    dsimp [p0]
    positivity
  have hTarget : 0<D+p0 := by linarith
  obtain ⟨J,B,S,hSB,hSave⟩ :=
    parity_eventually_original_actual_B509_full_chi_polynomial_ball_saving434
      jQ (D+p0) C0 Cf CZ Ck beta gamma hTarget hCZ hCk hbeta hgamma
  let BE : ℝ := 2*A*(P.factorial:ℝ)
  let BN : ℝ := 8*A^2*(P.factorial:ℝ)*(2:ℝ)^P+(P.factorial:ℝ)*A
  refine ⟨J,B,S,hSB,?_⟩
  filter_upwards [hSave,eventually_ge_atTop (8:ℝ),
    eventually_ge_atTop (6*Cbox),eventually_ge_atTop BE,
    eventually_ge_atTop BN] with L hSaveL hL hC hBE hBN
  refine ⟨hL,hC,hSaveL.1,hSaveL.2.1,?_⟩
  intro hLw hFamily Z hZlo hZhi band hBand slot delta freq k hk hkBound
    rho xi1 xi2 xi3 U E V T hU hV hUV hE hZhiPhysical hTCut
    hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu hub signed
  dsimp only
  let K := Finset.Icc a b
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let N := Finset.Icc 1 ⌊64*Z⌋₊
  let sourceF : DirichletCharacter ℂ (2*k.natAbs) → PrimeSlotCore := fun chi =>
    sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L)
      L band slot delta freq K alpha (2*k.natAbs) chi 0 0
  let original : EuclideanSpace ℝ (Fin 3) → ℂ := fun ζ =>
    ∑chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
        parityOriginalHistoricalActualB633FullFourierCofactor434
          L rho xi1 xi2 xi3 U Z k N alpha
          (sourceF chi).residual (2*k.natAbs) chi
          (sourceF chi).lo (sourceF chi).hi signed
          parityOriginalHistoricalDyadicSmoothPsi434 ζ
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  have hZ0 : 0≤Z := by
    have hLpos : 0<L := by linarith
    have hh : 0<Real.exp L*L^(-CZ) :=
      mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLpos _)
    exact (hh.trans_le hZlo).le
  have hM0 := parity_original_actual_capfree_Bprime_M0_uniform_polylog434
    L U E V Z K0 Cbox A hLw hK0 k hk hU hV hUV hE hZ0
    (by linarith : 0≤Cbox) hC hZhiPhysical hA buf hSmooth hSupport
    (by simpa only [Nat.zero_add] using hBE)
    (by simpa only [Nat.zero_add] using hBN) R hR hCube
  have hSpectral := hSaveL.2.2 hFamily Z hZlo hZhi band hBand
    slot delta freq k hk hkBound rho xi1 xi2 xi3 U T f
    hU hTCut hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu hub signed
  have hAbsorb := parity_original_actual_capfree_Bprime_primary_inverse_log_from_M0434
    L Z D K0 Cmoment (parityOriginal3DSourceMomentFiniteBudget434 0 f)
    hLw hZ0 hM0
  dsimp only at hSpectral hAbsorb ⊢
  exact hSpectral.trans hAbsorb
end Green64Analytic.Parity

end

end

/-! ## BPrimePrimaryNormalizedTwoGhost -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4900000

/-- Actual ORIGINAL cap-free Bprime all-odd post-Cauchy 3D source
LOW-frequency ball, now with the MAIN signed Parity(4.17) saving
numerically normalized to C_0 Z L^-D (no remaining abstract M0).
The genuine source eta_e/n moment is proved from the exact five
smooth factors with original upper z-height, under UV~exp L and
E=U L^-K0; J,B,S are fixed with target D+p0 BEFORE L.

The TWO independently source-paid ghost errors remain EXPLICIT, with
no forbidden signed-subset monotonicity. Full global k/Z/branch/fine
summation and Parity TypeII(4.2), §§5-9 and Green64 are not asserted. -/
theorem parity_eventually_original_actual_Bprime_lowfreq_primary_normalized_two_ghost434
    (jQ : ℕ) (D C0 Cf CZ Ck beta gamma K0 Cbox A R : ℝ)
    (hD : 0<D) (hCZ : 0≤CZ) (hCk : 0≤Ck)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, 8≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hLw : 8≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
        ∀ (rho xi1 xi2 xi3 U E V T : ℝ) (signed : Bool),
          0<U → 0<E → 0<V → Real.exp L≤U*V →
          E=U*L^(-K0) → Z≤24*Cbox*Real.exp L*L^(K0+88) →
          0<T → T≤L^Cf →
          |rho|≤L^C0 → |xi1|≤L^C0 → |xi2|≤L^C0 → |xi3|≤L^C0 →
          |((2*k:ℤ):ℝ)|≤Z/128 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L)≤(lFine:ℝ) →
          2≤lFine → uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
        ∀ (H : ℕ),
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let d := sourceOriginalLiteralDepth 20 L
        let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
        let N : Finset ℕ := Finset.Icc 1 ⌊64*Z⌋₊
        let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
          (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
        let At : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
          L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
          i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
        let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hLw U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport
        let sourceTerms : ℕ → Finset (ℕ × (ℕ × ℕ)) := fun m =>
          parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
            d L E V band slot delta (Nat.ceil (6*U*V)) m K k
        let phi : ℕ → (ℕ × (ℕ × ℕ)) → I :=
          parityOriginalHistoricalUngatedSourceToSigma434
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
            (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
              (∑m0∈K, ∑q∈sourceTerms m0,
                parityOriginalHistoricalDyadicSmoothPsi434
                  ((parityOriginalHistoricalCanonicalZ434 q.1 m0 q.2.1 q.2.2:ℝ)/Z) *
                alpha m0 * star (alpha q.2.1) *
                At (phi m0 q) *
                parityOriginal3DPhysicalLogFourierPhase434 ζ
                  (parityOriginalHistoricalRealLogTriple434 U Z
                    (phi m0 q).2.2 (phi m0 q).2.1 (phi m0 q).1))‖ ≤
        Cmoment*Z*L^(-D) +
          2*((L^(2*parityOriginalW1PolylogExponent434)*
            ((Nat.ceil (65*Z):ℕ):ℝ)*
            (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15)*
          (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)) := by
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let p0 : ℝ := 5*(K0+90)*((P:ℝ)+1)
  have hp0 : 0≤p0 := by
    have hK : 0≤K0+90 := by linarith
    have hp : 0≤(P:ℝ) := Nat.cast_nonneg _
    dsimp [p0]
    positivity
  have hTarget : 0<D+p0 := by linarith
  obtain ⟨J,B,S,hBS,hMain⟩ :=
    parity_eventually_original_actual_Bprime_full_odd_lowfreq_le_integrated_417_plus_two_ghost434
      jQ (D+p0) C0 Cf CZ Ck beta gamma hTarget hCZ hCk hbeta hgamma
  let BE : ℝ := 2*A*(P.factorial:ℝ)
  let BN : ℝ := 8*A^2*(P.factorial:ℝ)*(2:ℝ)^P+(P.factorial:ℝ)*A
  refine ⟨J,B,S,hBS,?_⟩
  filter_upwards [hMain,eventually_ge_atTop (6*Cbox),
    eventually_ge_atTop BE,eventually_ge_atTop BN]
    with L hMainL hC hBE hBN
  refine ⟨hMainL.1,hC,hMainL.2.1,hMainL.2.2.1,?_⟩
  intro hLw hFamily Z hZlo hZhi band hBand slot delta freq k hk hkBound
    rho xi1 xi2 xi3 U E V T signed hU hEpos hV hUV hE hZupper
    hT hTCut hrho hxi1 hxi2 hxi3 hkZ
    prime lFine uFine a b hFineLow hl hu hub hDyad H
  classical
  let K := Finset.Icc a b
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let d := sourceOriginalLiteralDepth 20 L
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let N : Finset ℕ := Finset.Icc 1 ⌊64*Z⌋₊
  let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let At : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let sourceTerms : ℕ → Finset (ℕ × (ℕ × ℕ)) := fun m =>
    parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot delta (Nat.ceil (6*U*V)) m K k
  let phi : ℕ → (ℕ × (ℕ × ℕ)) → I :=
    parityOriginalHistoricalUngatedSourceToSigma434
  have hZ0 : 0≤Z := by
    have hh : 0<Real.exp L*L^(-CZ) :=
      mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos (by linarith : 0<L) _)
    exact (hh.trans_le hZlo).le
  have hMoment := parity_original_actual_capfree_Bprime_M0_uniform_polylog434
    L U E V Z K0 Cbox A hLw hK0 k hk hU hV hUV hE hZ0
    (by linarith : 0≤Cbox) hC hZupper hA buf hSmooth hSupport
    (by simpa only [Nat.zero_add] using hBE)
    (by simpa only [Nat.zero_add] using hBN) R hR hCube
  have hAbsorb := parity_original_actual_capfree_Bprime_primary_inverse_log_from_M0434
    L Z D K0 Cmoment (parityOriginal3DSourceMomentFiniteBudget434 0 f)
    hLw hZ0 hMoment
  have hOld := hMainL.2.2.2 hLw hFamily Z hZlo hZhi band hBand slot delta freq
    k hk hkBound rho xi1 xi2 xi3 U E V T signed hU hEpos hV hT hTCut
    hrho hxi1 hxi2 hxi3 hkZ
    prime lFine uFine a b hFineLow hl hu hub hDyad
    buf (-Real.log A) (Real.log A) hSmooth hSupport H
  dsimp only at hOld hAbsorb ⊢
  exact hOld.trans (add_le_add_left hAbsorb _)
end Green64Analytic.Parity

end

end

/-! ## BPrimeTwoGhostPrecision -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 3600000

/-- The ACTUAL original Parity W1 loss exponent, based on its original
fixed P-group harmonic floor log(12/11)/4, is nonnegative. -/
theorem parity_original_actual_W1_polylog_exponent_nonneg434 :
    0 ≤ parityOriginalW1PolylogExponent434 := by
  have hFloor : 0 < parityOriginalW1GroupFloor434 := by
    unfold parityOriginalW1GroupFloor434
    exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hFloor2 : parityOriginalW1GroupFloor434 ≤ 2 := by
    unfold parityOriginalW1GroupFloor434
    have hLog := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 12/11)
    norm_num at hLog ⊢
    linarith
  have hRatio : (1:ℝ) ≤ 2/parityOriginalW1GroupFloor434 :=
    (le_div_iff₀ hFloor).mpr (by linarith)
  have hLn : 0 ≤ Real.log (2/parityOriginalW1GroupFloor434) :=
    Real.log_nonneg hRatio
  unfold parityOriginalW1PolylogExponent434
  positivity

/-- The TWO original actual paid ghost differences both become
`O(Z L^-D)` if one preselects one extra Fourier precision
`Dghost = D + 2 C_W1 + 30`; no hidden #characters, e, m, n.
This is the exact algebraic consequence of the already native-proven
real-source Parity(4.15) positive mass and real 3D M1 kernel bound. -/
theorem parity_original_actual_two_ghost_precision_algebra434
    (L Z D C1 Err : ℝ) (hL : 8 ≤ L)
    (hErr : Err ≤
      66*Z*C1*L^(2*parityOriginalW1PolylogExponent434+30-
        (D+2*parityOriginalW1PolylogExponent434+30))) :
    2*Err ≤ 132*Z*C1*L^(-D) := by
  have hLpos : 0 < L := by linarith
  have hPow :
      L^(2*parityOriginalW1PolylogExponent434+30-
        (D+2*parityOriginalW1PolylogExponent434+30))=L^(-D) := by
    congr 1
    ring
  have h2 := mul_le_mul_of_nonneg_left hErr (by norm_num : (0:ℝ) ≤ 2)
  calc
    2*Err ≤ 2*(66*Z*C1*L^(2*parityOriginalW1PolylogExponent434+30-
        (D+2*parityOriginalW1PolylogExponent434+30))) := h2
    _ = 132*Z*C1*L^(-D) := by rw [hPow]; ring
end Green64Analytic.Parity

end

end

/-! ## BPrimeFullOddFixedKZAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 5900000

/-- Exact ORIGINAL all-odd actual cap-free Bprime lowfrequency Fourier
ball, for every fixed k,Z, fine b629 K, source reserved Q band and slot,
with FULL paid ghosts and actual original five-factor ηeηn Schwartz
kernel, satisfies an arbitrarily deep L^-D saving with fixed ORIGINAL
source constant C0+132*C1. A SINGLE Fourier T=L^Cf is chosen before
J,B,S,L, where Cf pays H=1 source derivatives and W1/corr mass.
All actual χ are projected before cutting frequencies; no omitted
physical e/n/m counts or fake P-free e selection. This is a per-k,Z
and fine-cell theorem, NOT the global Parity TypeII (4.2). -/
theorem parity_eventually_original_actual_Bprime_full_odd_fixed_KZ_any_log_saving434
    (jQ : ℕ) (D C0 Cf CZ Ck beta gamma K0 Cbox A R : ℝ)
    (hD : 0<D)
    (hCf : Cf = (5*(K0+90))*
      ((((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) +
      (D+2*parityOriginalW1PolylogExponent434+30))
    (hCZ : 0≤CZ) (hCk : 0≤Ck)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, 8≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hLw : 8≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
        ∀ (rho xi1 xi2 xi3 U E V T : ℝ) (signed : Bool),
          0<U → 0<E → 0<V → Real.exp L≤U*V →
          E=U*L^(-K0) → Z≤24*Cbox*Real.exp L*L^(K0+88) →
          T=L^Cf →
          |rho|≤L^C0 → |xi1|≤L^C0 → |xi2|≤L^C0 → |xi3|≤L^C0 →
          |((2*k:ℤ):ℝ)|≤Z/128 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L)≤(lFine:ℝ) →
          2≤lFine → uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let d := sourceOriginalLiteralDepth 20 L
        let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
        let N : Finset ℕ := Finset.Icc 1 ⌊64*Z⌋₊
        let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
          (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
        let At : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
          L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
          i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
        let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hLw U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport
        let sourceTerms : ℕ → Finset (ℕ × (ℕ × ℕ)) := fun m =>
          parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
            d L E V band slot delta (Nat.ceil (6*U*V)) m K k
        let phi : ℕ → (ℕ × (ℕ × ℕ)) → I :=
          parityOriginalHistoricalUngatedSourceToSigma434
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
            (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
              (∑m0∈K, ∑q∈sourceTerms m0,
                parityOriginalHistoricalDyadicSmoothPsi434
                  ((parityOriginalHistoricalCanonicalZ434 q.1 m0 q.2.1 q.2.2:ℝ)/Z) *
                alpha m0 * star (alpha q.2.1) *
                At (phi m0 q) *
                parityOriginal3DPhysicalLogFourierPhase434 ζ
                  (parityOriginalHistoricalRealLogTriple434 U Z
                    (phi m0 q).2.2 (phi m0 q).2.1 (phi m0 q).1))‖ ≤
        (Cmoment+132*Cmoment1)*Z*L^(-D) := by
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let X : ℝ := (5*(K0+90))*(((1+P:ℕ):ℝ)+1)
  let Dghost : ℝ := D+2*parityOriginalW1PolylogExponent434+30
  have hCW : 0≤parityOriginalW1PolylogExponent434 :=
    parity_original_actual_W1_polylog_exponent_nonneg434
  have hDghost : 0≤Dghost := by dsimp [Dghost]; linarith
  have hCfX : Cf = X+Dghost := by simpa only [X,Dghost] using hCf
  obtain ⟨J,B,S,hBS,hMain⟩ :=
    parity_eventually_original_actual_Bprime_lowfreq_primary_normalized_two_ghost434
      jQ D C0 Cf CZ Ck beta gamma K0 Cbox A R
      hD hCZ hCk hbeta hgamma hK0 hCbox hA hR
      buf hSmooth hSupport hCube
  have hGhost := parity_eventually_original_Bprime_two_ghost_scaled_tail434
    CZ Ck hCZ
  let J1 : ℕ := 1+P
  let BE1 : ℝ := 2*A*(J1.factorial:ℝ)
  let BN1 : ℝ := 8*A^2*(J1.factorial:ℝ)*(2:ℝ)^J1+(J1.factorial:ℝ)*A
  refine ⟨J,B,S,hBS,?_⟩
  filter_upwards [hMain,hGhost,eventually_ge_atTop BE1,
    eventually_ge_atTop BN1] with L hMainL hGhostL hBE1 hBN1
  refine ⟨hMainL.1,hMainL.2.1,hMainL.2.2.1,hMainL.2.2.2.1,?_⟩
  intro hLw hFamily Z hZlo hZhi band hBand slot delta freq k hk hkBound
    rho xi1 xi2 xi3 U E V T signed hU hEpos hV hUV hE hZupper
    hTscale hrho hxi1 hxi2 hxi3 hkZ
    prime lFine uFine a b hFineLow hl hu hub hDyad
  classical
  let K := Finset.Icc a b
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let d := sourceOriginalLiteralDepth 20 L
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let N : Finset ℕ := Finset.Icc 1 ⌊64*Z⌋₊
  let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let At : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let sourceTerms : ℕ → Finset (ℕ × (ℕ × ℕ)) := fun m =>
    parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot delta (Nat.ceil (6*U*V)) m K k
  let phi : ℕ → (ℕ × (ℕ × ℕ)) → I :=
    parityOriginalHistoricalUngatedSourceToSigma434
  have hLpos : 0<L := by linarith
  have hTpos : 0<T := by
    rw [hTscale]
    exact Real.rpow_pos_of_pos hLpos _
  have hTCut : T≤L^Cf := by rw [hTscale]
  have hTghost : T=L^(X+Dghost) := by rw [hTscale,hCfX]
  have hGhostBound := hGhostL.2 hLw Z hZlo hZhi k hk hkBound
    Dghost U E V K0 Cbox A hDghost hK0 hU hV hUV hE
    (by linarith : 0≤Cbox) hMainL.2.1 hZupper hA
    buf hSmooth hSupport
    (by simpa only [J1] using hBE1)
    (by simpa only [J1] using hBN1)
    R hR hCube
  let Err : ℝ :=
    (L^(2*parityOriginalW1PolylogExponent434)*
      ((Nat.ceil (65*Z):ℕ):ℝ)*
      (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15)*
      (parityOriginal3DSourceMomentFiniteBudget434 1 f/T)
  have hErr : Err≤66*Z*Cmoment1*
      L^(2*parityOriginalW1PolylogExponent434+30-Dghost) := by
    dsimp only [Err]
    rw [hTghost]
    convert hGhostBound using 1
  have hTwoGhost : 2*Err≤132*Z*Cmoment1*L^(-D) :=
    parity_original_actual_two_ghost_precision_algebra434
      L Z D Cmoment1 Err hLw (by simpa only [Dghost] using hErr)
  have hMainBound := hMainL.2.2.2.2 hLw hFamily Z hZlo hZhi band hBand
    slot delta freq k hk hkBound rho xi1 xi2 xi3 U E V T signed
    hU hEpos hV hUV hE hZupper hTpos hTCut
    hrho hxi1 hxi2 hxi3 hkZ
    prime lFine uFine a b hFineLow hl hu hub hDyad 1
  dsimp only at hMainBound hTwoGhost ⊢
  calc
    _ ≤ Cmoment*Z*L^(-D)+2*Err := by
      simpa only [Err,pow_one] using hMainBound
    _ ≤ Cmoment*Z*L^(-D)+132*Z*Cmoment1*L^(-D) :=
      add_le_add_right hTwoGhost _
    _ = (Cmoment+132*Cmoment1)*Z*L^(-D) := by ring
end Green64Analytic.Parity

end

end

/-! ## BPrimeActualKZGlobalFine -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The ACTUAL, literal B' full-odd low-frequency source signal,
not a new analytic majorant. The fixed parameters include the actual
fine b629 alpha and original source Q/P labels. Its fibre counts
one natural e,n,m,m',z source event with its true multiplicity; the
full character mask has already been inserted in the original atom.
The cutoff f is the original five-factor Parity (4.14) Schwartz kernel. -/
def parityOriginalActualBprimeFineLowfreqSignal434
    (d : ℕ) (L U E V : ℝ) (hLw : 8≤L) (Z : ℝ) (k : ℤ)
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (rho xi1 xi2 xi3 T : ℝ) (signed : Bool)
    (buf : ℝ → ℂ) (A : ℝ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A) : ℂ :=
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let At : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport
  let sourceTerms : ℕ → Finset (ℕ × (ℕ × ℕ)) := fun m =>
    parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot delta (Nat.ceil (6*U*V)) m K k
  let phi : ℕ → (ℕ × (ℕ × ℕ)) → I :=
    parityOriginalHistoricalUngatedSourceToSigma434
  ∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
    (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
      (∑m0∈K, ∑q∈sourceTerms m0,
        parityOriginalHistoricalDyadicSmoothPsi434
          ((parityOriginalHistoricalCanonicalZ434 q.1 m0 q.2.1 q.2.2:ℝ)/Z) *
        alpha m0 * star (alpha q.2.1) *
        At (phi m0 q) *
        parityOriginal3DPhysicalLogFourierPhase434 ζ
          (parityOriginalHistoricalRealLogTriple434 U Z
            (phi m0 q).2.2 (phi m0 q).2.1 (phi m0 q).1))

/-- Native Parity(4.17) spectral saving for the genuinely original
signed k and attained binary Z outer, for ONE reserved Q band/slot,
ONE fine b629 interval and ONE original allocation (delta,freq).
Unlike a generic finite-sum lemma, the summand here is literally the
whole five-factor B' complex Fourier ball from the preceding production
root. The total loss is only (2N+1)(floor(log2 Y)+1), with no count
of e,n,m,m',z or characters. This is NOT the full original TypeII,
which still requires source restrictions and remaining outer families. -/
theorem parity_eventually_original_actual_Bprime_fine_global_kZ_norm434
    (jQ : ℕ) (D C0 Cf CZ Ck beta gamma K0 Cbox A R : ℝ)
    (hD : 0<D)
    (hCf : Cf = (5*(K0+90))*
      ((((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) +
      (D+2*parityOriginalW1PolylogExponent434+30))
    (hCZ : 0≤CZ) (hCk : 0≤Ck)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, 8≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hLw : 8≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (rho xi1 xi2 xi3 U E V T : ℝ) (signed : Bool),
          0<U → 0<E → 0<V → Real.exp L≤U*V → E=U*L^(-K0) →
          T=L^Cf →
          |rho|≤L^C0 → |xi1|≤L^C0 → |xi2|≤L^C0 → |xi3|≤L^C0 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L)≤(lFine:ℝ) →
          2≤lFine → uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
        ∀ (KS : Finset ℤ) (N Y : ℕ) (ZS : Finset ℕ),
          (∀k∈KS, k≠0 ∧ k.natAbs≤N ∧ (k.natAbs:ℝ)≤L^Ck) →
          (∀z∈ZS, 0<z ∧ z≤Y) →
          (∀Z∈ZS.image parityOriginalHistoricalActualZDyadicScale434,
            Real.exp L*L^(-CZ)≤(Z:ℝ) ∧
            (Z:ℝ)≤Real.exp L*L^CZ ∧
            (Z:ℝ)≤24*Cbox*Real.exp L*L^(K0+88)) →
          (∀k∈KS,∀Z∈ZS.image parityOriginalHistoricalActualZDyadicScale434,
            |((2*k:ℤ):ℝ)|≤(Z:ℝ)/128) →
        let d := sourceOriginalLiteralDepth 20 L
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        ‖∑k∈KS,∑Z∈ZS.image parityOriginalHistoricalActualZDyadicScale434,
          parityOriginalActualBprimeFineLowfreqSignal434
            d L U E V hLw (Z:ℝ) k band slot delta freq K alpha
            rho xi1 xi2 xi3 T signed buf A hSmooth hSupport‖ ≤
          (((2*N+1:ℕ):ℝ)*((Nat.log 2 Y+1:ℕ):ℝ))*
            (Cmoment+132*Cmoment1)*(Y:ℝ)*L^(-D) := by
  obtain ⟨J,B,S,hBS,hLocal⟩ :=
    parity_eventually_original_actual_Bprime_full_odd_fixed_KZ_any_log_saving434
      jQ D C0 Cf CZ Ck beta gamma K0 Cbox A R
      hD hCf hCZ hCk hbeta hgamma hK0 hCbox hA hR
      buf hSmooth hSupport hCube
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  have hC0 : 0≤Cmoment :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 0 hR
  have hC1 : 0≤Cmoment1 :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 1 hR
  have hC : 0≤Cmoment+132*Cmoment1 := by linarith
  refine ⟨J,B,S,hBS,?_⟩
  filter_upwards [hLocal] with L hL
  refine ⟨hL.1,hL.2.1,hL.2.2.1,hL.2.2.2.1,?_⟩
  intro hLw hFamily band hBand slot delta freq rho xi1 xi2 xi3
    U E V T signed hU hEpos hV hUV hEscale hT hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu huExp hDyad
    KS N Y ZS hKS hZS hZwindow hkZwindow
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let K := Finset.Icc a b
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let F : ℤ → ℕ → ℂ := fun k Z =>
    parityOriginalActualBprimeFineLowfreqSignal434
      d L U E V hLw (Z:ℝ) k band slot delta freq K alpha
      rho xi1 xi2 xi3 T signed buf A hSmooth hSupport
  have hKBound : ∀k∈KS,k.natAbs≤N := by
    intro k hk
    exact (hKS k hk).2.1
  have hZBound : ∀z∈ZS,z≤Y := by
    intro z hz
    exact (hZS z hz).2
  have hZPositive : ∀z∈ZS,0<z := by
    intro z hz
    exact (hZS z hz).1
  have hPosL : 0<L := by linarith
  have hCell : ∀k∈KS,∀Z∈ZS.image parityOriginalHistoricalActualZDyadicScale434,
      ‖F k Z‖≤(Cmoment+132*Cmoment1)*(Z:ℝ)*L^(-D) := by
    intro k hk Z hz
    have hkk := hKS k hk
    have hzz := hZwindow Z hz
    have hkz := hkZwindow k hk Z hz
    have hOne := hL.2.2.2.2 hLw hFamily (Z:ℝ) hzz.1 hzz.2.1
      band hBand slot delta freq k hkk.1 hkk.2.2
      rho xi1 xi2 xi3 U E V T signed
      hU hEpos hV hUV hEscale hzz.2.2 hT
      hrho hxi1 hxi2 hxi3 hkz
      prime lFine uFine a b hFineLow hl hu huExp hDyad
    dsimp only at hOne ⊢
    change ‖F k Z‖ ≤ (Cmoment+132*Cmoment1)*(Z:ℝ)*L^(-D)
    simpa only [F,parityOriginalActualBprimeFineLowfreqSignal434] using hOne
  have hSum :=
    parity_original_actual_signed_k_dyadic_z_global_norm_bound434
      L D (Cmoment+132*Cmoment1) hPosL hC KS N hKBound ZS Y hZBound
      hZPositive F hCell
  simpa only [F,d,K,alpha,Cmoment,Cmoment1] using hSum
end Green64Analytic.Parity

end

end

/-! ## SmoothPsiNeighborZ -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- For the TRUE source smooth ψ with support 1<t<4, each original
positive physical z may contribute at its canonical binary scale
or at the immediately preceding half-scale. A single hard Z(z)
image would omit a real term of the smooth dyadic partition. -/
def parityOriginalActualSmoothPsiNeighborZEnvelope434 (S : Finset ℕ) : Finset ℕ :=
  (S.image parityOriginalHistoricalActualZDyadicScale434) ∪
  (S.image (fun z => parityOriginalHistoricalActualZDyadicScale434 z / 2))

/-- SOURCE-TRUE no-missing-smooth-pieces assertion: if the actual
C∞ ψ(z/2^j) is nonzero then 2^j is canonically attached to z OR
the preceding half-dyad. No hard-mask replacement of ψ occurs. -/
theorem parity_original_actual_smooth_psi_dyadic_nonzero_neighbor434
    (S : Finset ℕ) (z j : ℕ) (hz : z∈S)
    (hpsi : parityOriginalHistoricalDyadicSmoothPsi434
      ((z:ℝ)/(2:ℝ)^j) ≠ 0) :
    (2:ℕ)^j ∈ parityOriginalActualSmoothPsiNeighborZEnvelope434 S := by
  classical
  have hΨ := parity_original_historical_dyadic_psi_compact_positive_support434
    ((z:ℝ)/(2:ℝ)^j) hpsi
  have hzpos : 0<z := by
    by_contra hh
    have hz0 : z=0 := Nat.eq_zero_of_not_pos hh
    subst z
    norm_num at hΨ
  let q := Nat.log 2 z
  have hOwn := parity_original_historical_actual_z_in_own_dyad434 z hzpos
  have hqzNat : (2:ℕ)^q ≤ z := by
    simpa only [q,parityOriginalHistoricalActualZDyadicScale434] using hOwn.2.1
  have hzqNat : z < 2*(2:ℕ)^q := by
    simpa only [q,parityOriginalHistoricalActualZDyadicScale434] using hOwn.2.2
  have hqz : (2:ℝ)^q ≤ (z:ℝ) := by exact_mod_cast hqzNat
  have hzq : (z:ℝ) < (2:ℝ)^(q+1) := by
    have hh : (z:ℝ) < 2*(2:ℝ)^q := by exact_mod_cast hzqNat
    rw [pow_succ]
    nlinarith
  have hzp : 0<(2:ℝ)^j := by positivity
  have hJupper : (2:ℝ)^j < (z:ℝ) := by
    have hh := (lt_div_iff₀ hzp).mp hΨ.1
    nlinarith
  have hJlower : (z:ℝ) < (2:ℝ)^(j+2) := by
    have hh := (div_lt_iff₀ hzp).mp hΨ.2
    have hPow : (2:ℝ)^(j+2)=4*(2:ℝ)^j := by
      rw [pow_add]
      norm_num
      ring
    rw [hPow]
    nlinarith
  have hjle : j≤q := by
    by_contra hh
    have hqj : q+1≤j := by omega
    have hPow : (2:ℝ)^(q+1)≤(2:ℝ)^j := by gcongr; norm_num
    linarith
  have hqle : q≤j+1 := by
    by_contra hh
    have hjq : j+2≤q := by omega
    have hPow : (2:ℝ)^(j+2)≤(2:ℝ)^q := by gcongr; norm_num
    linarith
  have hCase : j=q ∨ j+1=q := by omega
  unfold parityOriginalActualSmoothPsiNeighborZEnvelope434
  rcases hCase with heq | heq
  · apply Finset.mem_union.mpr
    left
    exact Finset.mem_image.mpr ⟨z,hz,by simp [parityOriginalHistoricalActualZDyadicScale434,q,heq]⟩
  · apply Finset.mem_union.mpr
    right
    apply Finset.mem_image.mpr
    refine ⟨z,hz,?_⟩
    change (2:ℕ)^q/2 = (2:ℕ)^j
    rw [←heq,pow_succ]
    omega

/-- Even after restoring the necessary neighboring ψ dyads, the
number of DISTINCT active Fourier height scales stays logarithmic,
with exact multiplicative cost 2 rather than #physical z-tuples. -/
theorem parity_original_actual_smooth_psi_neighbor_card_le434
    (S : Finset ℕ) (Y : ℕ) (hY : ∀z∈S,z≤Y) :
    (parityOriginalActualSmoothPsiNeighborZEnvelope434 S).card ≤
      2*(Nat.log 2 Y+1) := by
  classical
  let A := S.image parityOriginalHistoricalActualZDyadicScale434
  let B := S.image (fun z => parityOriginalHistoricalActualZDyadicScale434 z/2)
  have hA : A.card≤Nat.log 2 Y+1 :=
    parity_original_actual_dyadic_z_image_card_le_log434 S Y hY
  have hB : B.card≤A.card := by
    have hEq : B = A.image (fun Z : ℕ => Z/2) := by
      dsimp [A,B]
      ext t
      simp [A,B,Finset.mem_image,Function.comp_def]
    rw [hEq]
    exact Finset.card_image_le
  change (A∪B).card≤_
  calc
    _ ≤ A.card+B.card := Finset.card_union_le _ _
    _ ≤ 2*(Nat.log 2 Y+1) := by omega
end Green64Analytic.Parity

end

end

