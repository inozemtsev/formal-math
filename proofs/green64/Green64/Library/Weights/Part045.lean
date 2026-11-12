module

public import Green64.Library.Correlation.Part033
public import Green64.Library.Weights.Part033
public import Green64.Library.Analysis.Estimates.Part002
public import Green64.Library.Weights.Part016
public import Green64.Library.Correlation.Part002
public import Green64.Library.Weights.Part023
public import Green64.Library.Correlation.Part001
public import Green64.Library.Weights.Part042
public import Green64.Library.Analysis.PrimeNumberTheorem.Part003
public import Mathlib
public import Green64.Library.Weights.Part012
public import Green64.Library.Weights.Part013
public import Green64.Library.Weights.Part003

@[expose] public section

/-!
# Weights / Part045

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalArcSaving -/

section

open MeasureTheory Filter
open scoped BigOperators FourierTransform SchwartzMap ContDiff RealInnerProductSpace
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option maxHeartbeats 20000000

/-- Genuine original FULL arc saving from source discrepancy. All auxiliary
kernels, amplitude caps, harmonic mass and decay orders are discharged.
The source identity Y=Z*Hprime supplies replacement smallness. -/
theorem eventually_source_original_arc_conclusion434
    (aexp bexp cexp Carc CZ τ η Cχ C0 q0 vmin : ℝ)
    (tmax ea ec s0 cm target s1base vexp fcut epsi : ℕ)
    (A Cpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hA : 1 ≤ A) (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j)
    (hepsi : 3*Cpsi ≤ (epsi:ℝ)) (hFcut : Cpsi+2 < (fcut:ℝ))
    (haexp : 0 < aexp) (hab : aexp < bexp) (hb : bexp < 1)
    (hbc : bexp < cexp)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hCχ : 0 < Cχ) (hC0 : 0 ≤ C0) (hCarc : 0 ≤ Carc)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ Kout : ℝ, 0 < Kout ∧ ∃ B : ℕ, ∃ X0 : ℝ, 3 ≤ X0 ∧
      ∀ᶠ L : ℝ in atTop,
      ∀ (x : ℝ), X0 ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (Y Hprime Z : ℝ),
      4 ≤ Y → Y ≤ Real.exp (3*L/2) → 0 < Hprime →
      Real.exp (3*L/4) ≤ Y →
      x*L^(-CZ) ≤ Z → Y = Z*Hprime →
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β],
      (Fintype.card ι:ℝ) ≤ C0*Real.log L →
      (Fintype.card β:ℝ) ≤ C0*Real.log L →
      ∀ (lo hi Ncap : ℕ) (alpha : ℕ → ℂ),
      (Ncap:ℝ) ≤ x^2 → A*Y ≤ (Ncap:ℝ) →
      (∀ m ∈ Finset.Icc lo hi, ‖alpha m‖ ≤ L^ea) →
      SourceAlphaDiscrepancy L (B:ℝ) x alpha →
      ∀ (G Parity S primeSlot : Finset ℕ)
        (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k qBase den h : ℕ)
        (c : ℕ → ℂ) (chi0 : DirichletCharacter ℂ qBase),
      0 < qBase → 0 < den →
      (qBase:ℝ) ≤ L^cm → (den:ℝ) ≤ L^cm →
      (den:ℝ) ≤ L^Cχ →
      k+1 ≤ tmax → vmin ≤ Vs →
      (∀ j : ι, ts j ≤ tmax) → (∀ j : β, tb j ≤ tmax) →
      (∀ j : ι, vmin ≤ Vsmall j) → (∀ j : β, vmin ≤ Vbig j) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (C : ℝ), 0 ≤ C → C ≤ L^ec → (∀ n, ‖c n‖ ≤ C) →
      ∀ (sigma0 sigma1 : ℝ),
      |sigma0| ≤ L^s0 → |sigma1| ≤ L^s1base →
      ∀ (W : ℝ),
      ((qBase*den:ℕ):ℝ) ≤ W →
      S ⊆ G → (∀ v ∈ S, v.Prime) →
      (∀ v ∈ S, v ≤ Ncap) →
      (∀ p ∈ primeSlot, p ≤ Ncap) →
      (∀ m, sourceAlphaDyadicCut alpha lo hi m ≠ 0 → SourceRoughAbove m W) →
      (∀ v ∈ G, (v:ℝ) ≤ W) →
      (∀ p ∈ primeSlot, W < (p:ℝ)) →
      ∀ (I : Set ℝ),
      Set.OrdConnected I →
      (∀ s ∈ S, Real.exp (L^aexp) ≤ (s:ℝ) ∧ (s:ℝ) ≤ Real.exp (L^bexp)) →
      (∀ p, p ∈ primeSlot ↔ p.Prime ∧ (p:ℝ) ∈ I) →
      I ⊆ Set.Icc (x^τ) (x^η) →
      ∀ {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂]
        (F1 : Finset ι₁) (F2 : Finset ι₂)
        (p1 : ι₁ → ℕ) (p2 : ι₂ → ℕ) (U1 U2 : ℝ),
      F1.Nonempty → F2.Nonempty →
      (∀ i ∈ F1, 1 ≤ p1 i) → (∀ i ∈ F2, 1 ≤ p2 i) →
      (∀ i ∈ F1, Real.exp (L^cexp) ≤ (p1 i:ℝ)) →
      (∀ i ∈ F2, Real.exp (L^cexp) ≤ (p2 i:ℝ)) →
      0 < U1 → 0 < U2 →
      Real.log (((∏ i ∈ F1, p1 i : ℕ):ℝ)) ≤ Real.log U1+1 →
      Real.log (((∏ i ∈ F2, p2 i : ℕ):ℝ)) ≤ Real.log U2+1 →
      Hprime = U1*U2 →
      ∀ (psi1 : ℝ → ℂ),
      ContDiff ℝ ∞ psi1 →
      (∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A) →
      ∀ (v1 : ℝ), |v1| ≤ L^vexp →
      sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi1 (Real.exp u)) →
      G = S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
        ((Finset.univ : Finset β).biUnion Tb) → Parity ⊆ G →
      (∀ g, ∀ p ∈ Ts g, p.Prime) → (∀ g, ∀ p ∈ Tb g, p.Prime) →
      (∀ m, sourceAlphaDyadicCut alpha lo hi m ≠ 0 →
        SourceRoughAbove m (Real.exp (Real.sqrt L))) →
      (den:ℝ) ≤ L^Carc → L^Carc ≤ Real.exp (Real.sqrt L) →
      L^Carc < Real.exp (L^aexp) → L^Carc < Real.exp (τ*L) →
      (∀ p ∈ primeSlot, Real.exp (τ*L) ≤ (p:ℝ)) →
      2 ≤ Hprime/L^Carc → Hprime/L^Carc ≤ Y/(8*A) →
      (∀ g, ∀ p ∈ S, p ∉ Ts g) → (∀ g, ∀ p ∈ S, p ∉ Tb g) →
      SourceOriginalArcConclusion434 Ncap qBase S Ts Tb q0 Vs Vsmall Vbig
        ts tb coef k primeSlot Parity (sourceAlphaDyadicCut alpha lo hi) c
        chi0 sigma0 sigma1 (fun n => psi1 ((n:ℝ)/Y)*sourcePhase n v1)
        L Y Hprime Carc (target:ℝ) Kout h den := by
  obtain ⟨Ksq,hKsq,δ,M,cb,hδ,hδ1,hM,hcb,Kg,hKg,hFamily⟩ :=
    eventually_source_original_full_additive434
      aexp bexp cexp Carc τ η Cχ C0 q0 vmin
      tmax ea ec s0 cm (target+2*cm+8) s1base vexp fcut epsi A Cpsi Kpsi
      hA hCpsi hKpsi hepsi hFcut haexp hab hb hbc hτ hτη hη hCχ hC0 hq0 hq1 hv
  let E : ℝ := Cpsi+(ea:ℝ)+(ec:ℝ)+2*C0*Real.log Kg
  let Es : ℝ := Cpsi+(ea:ℝ)+(ec:ℝ)+2*C0*Real.log Ksq+1
  let B0 : ℝ := Kpsi 0*Kg/vmin
  let Bs0 : ℝ := Kpsi 0*Ksq*(1+2/(vmin*Real.log 2))
  have hK0 := hKpsi 0
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogA : 0 ≤ Real.log (2*A) := Real.log_nonneg (by linarith)
  have hB0 : 0 ≤ B0 := by dsimp [B0]; positivity
  have hBs0 : 0 ≤ Bs0 := by dsimp [Bs0]; positivity
  let j : ℕ := Nat.ceil (2*E+64+(target:ℝ))+2
  have hj : 2 ≤ j := by dsimp [j]; omega
  have hOrder : 2*E+64+(target:ℝ) ≤ ((j-2:ℕ):ℝ) := by
    simpa only [j,Nat.add_sub_cancel] using Nat.le_ceil (2*E+64+(target:ℝ))
  obtain ⟨K,hK,B,X0,hX0,hOriginal⟩ := hFamily j hj
  let Cl : ℝ := (1/vmin)^2*(1+2/Real.log 2)^8
  let Ct : ℝ := (8*A*(1+32*A*(Real.log (2*A)+5/2))*(Real.log (2*A)+5/2)^63)*B0^2
  have hCl : 0 ≤ Cl := by dsimp [Cl]; positivity
  have hCt : 0 ≤ Ct := by dsimp [Ct]; positivity
  let Kout : ℝ := (4*K*(Cl+Ct)+4+2*cb^2)/cb^2
  have hKout : 0 < Kout := by dsimp [Kout]; positivity
  refine ⟨Kout,hKout,B,X0,hX0,?_⟩
  have hRep := eventually_source_arc_replacement_saving434 A Carc CZ
    (4*δ*(4*δ+1)*(16*A*δ^2*M)^2) B0 E (target:ℝ)
    hA hCarc (by positivity) hB0
  have hSq := eventually_source_arc_square_saving434 A aexp Bs0 Es 3 1 (target:ℝ)
    hA haexp hBs0 (by norm_num)
  filter_upwards [hOriginal,hRep,hSq] with L hOriginalL hRepL hSqL
  intro x hx hLog hL Y Hprime Z hY hYmax hH hYstrong hZ hYIdent
  intro ι β _ _ _ _ hSmallGroups hBigGroups lo hi Ncap alpha hNcap hCap hAlpha hDisc
  intro G Parity S primeSlot Ts Tb Vs Vsmall Vbig ts tb coef k qBase den h c chi0
    hBase hden0 hBaseCap hDenCap hDenChar hk hVs hts htb hVsmall hVbig hcoef
    C hC hCBudget hcBound sigma0 sigma1 hSigma0 hSigma1 W hModW hSG hSPrime
    hSN hPN hRough hGroup hLong I hI hSmall hSlot hIBand
  intro ι₁ ι₂ _ _ F1 F2 p1 p2 U1 U2 hF1 hF2 hp1 hp2 hmin1 hmin2
    hU1 hU2 hcell1 hcell2 hHIdent
  intro psi1 hSmooth hSupport v1 hv1 hBudget
  intro hG hParity hTsPrime hTbPrime hRoughOriginal hDenOriginal
    hOrigW hOrigSmall hOrigLong hSlotMin hHband hArcCap hDisjS hDisjB
  have hLp : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hYp : 0 < Y := by linarith
  have hYone : 1 ≤ Y := by linarith
  have hxp : 0 < x := by linarith
  have hLogY : Real.log Y ≤ (3/2:ℝ)*L := by
    have hh := Real.log_le_log hYp hYmax
    rw [Real.log_exp] at hh
    linarith
  let Bpsi : ℝ := Kpsi 0*L^Cpsi
  have hBpsi : 0 ≤ Bpsi := by dsimp [Bpsi]; positivity
  have hPsiCap : ∀ n ∈ Finset.Icc 1 Ncap, ‖psi1 ((n:ℝ)/Y)‖ ≤ Bpsi := by
    intro n hn
    exact source_original_cutoff_sup434 Cpsi L Y Kpsi psi1 hYp hBudget n
      (Finset.mem_Icc.mp hn).1
  have hAY : 1 ≤ A*Y := by nlinarith
  have hNpos : 0 < Ncap := Nat.cast_pos.mp (lt_of_lt_of_le zero_lt_one (hAY.trans hCap))
  have hHarmonic := source_original_group_harmonic_budget434 S Ncap x L
    hNpos hxp hLone hLog hNcap (fun p hp => ⟨(hSPrime p hp).pos,hSN p hp⟩)
  have hRaw := hOriginalL x hx hLog hL Y Hprime hY hYmax hH hYstrong
    hSmallGroups hBigGroups lo hi Ncap alpha hNcap hCap hAlpha hDisc
    G Parity S primeSlot Ts Tb Vs Vsmall Vbig ts tb coef k qBase den h c chi0
    hBase hden0 hBaseCap hDenCap hDenChar hk hVs hts htb hVsmall hVbig hcoef
    C hC hCBudget hcBound sigma0 sigma1 hSigma0 hSigma1 W hModW hSG hSPrime
    hSN hPN hRough hGroup hLong I hI hSmall hSlot hIBand
    F1 F2 p1 p2 U1 U2 hF1 hF2 hp1 hp2 hmin1 hmin2
    hU1 hU2 hcell1 hcell2 hHIdent
    psi1 hSmooth hSupport v1 hv1 hBudget hden0
    (fun u hu => (hSupport u hu).2) Bpsi hBpsi hPsiCap
    hG hParity hTsPrime hTbPrime hRoughOriginal hDenOriginal
    hOrigW hOrigSmall hOrigLong hSlotMin hHband hArcCap hDisjS hDisjB (3*L) hHarmonic
  let Bamp : ℝ := Bpsi*(L^ea*C*(1/Vs)*Kg^(Fintype.card ι+Fintype.card β+1))
  let Bs : ℝ := Bpsi*(L^ea*C*(Ksq^(Fintype.card ι+Fintype.card β+1)*L*(1+2/(vmin*Real.log 2))))
  have hVp : 0 < Vs := hv.trans_le hVs
  have hBamp : 0 ≤ Bamp := by dsimp [Bamp]; positivity
  have hBs : 0 ≤ Bs := by dsimp [Bs]; positivity
  have hAmp := source_original_amplitude_budget434 L Kg C0 (Kpsi 0) Cpsi Bpsi C Vs vmin
    ea ec (Fintype.card ι) (Fintype.card β) hLone hKg hC0 hK0 hBpsi hC hv hVs
    le_rfl hCBudget hSmallGroups hBigGroups
  change Bamp ≤ B0*L^E at hAmp
  have hSqAmp := source_original_square_amplitude_budget434 L Ksq C0 (Kpsi 0) Cpsi Bpsi C vmin
    ea ec (Fintype.card ι) (Fintype.card β) hLone hKsq hC0 hK0 hBpsi hC hv
    le_rfl hCBudget hSmallGroups hBigGroups
  change Bs ≤ Bs0*L^Es at hSqAmp
  let H : ℝ := Hprime/L^Carc
  let N : ℝ := (Nat.ceil (A*Y):ℝ)
  let Budget : ℝ := Y*(L^target)⁻¹
  let low : ℝ := Y*((1/Vs)^2*(den:ℝ)^2*(((Ncap.log2+1)^4:ℕ):ℝ)^2*
    (L^(target+2*cm+8))⁻¹)
  let tail : ℝ := (1/Y)*((4*((L^(j-2))⁻¹*(L*Y/H+16*N*(1+Real.log N)))))*
    (Bamp^2*N*(1+Real.log N)^63)
  let rep : ℝ := 4*δ*(4*δ+1)*(16*A*δ^2*M)^2*(H/Y)^2*
    (Bamp^2*N*(1+Real.log N)^63)
  let square : ℝ := (3*L)*(Bs^2*N*(1+Real.log N)^16)*Real.exp (-(L^aexp))
  let squareRaw : ℝ := Bpsi^2*(3*L)*(L^ea*C*(Ksq^(Fintype.card ι+Fintype.card β+1)*
    L*(1+2/(vmin*Real.log 2))))^2*N*(1+Real.log N)^16*Real.exp (-(L^aexp))
  have hSquareEq : squareRaw = square := by dsimp only [squareRaw,square,Bs]; ring
  have hLow0 := source_original_arc_low_budget434 Ncap den cm target x L Y Vs vmin
    hNpos hxp hLog hLone hNcap hYp.le hv hVs hDenCap
  have hLow : low ≤ Cl*Budget := by simpa only [low,Cl,Budget,mul_assoc] using hLow0
  have hTail0 := source_arc_explicit_tail_saving434 A Y H L Bamp B0 E j target
    hA hYone (by dsimp [H]; linarith) hLone hLogY hBamp hB0 hAmp hOrder
  have hRadiusAlg : L/(H/Y) = L*Y/H := by
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]; ring
  rw [hRadiusAlg] at hTail0
  have hTail : tail ≤ Ct*Budget := by
    simpa only [tail,N,Ct,Budget,mul_assoc] using hTail0
  have hRep0 := hRepL.2 x Z Hprime Y Bamp hxp hLog hZ hH hYIdent hYone hLogY hBamp hAmp
  have hRepBound : rep ≤ Budget := by
    simpa only [rep,H,N,Budget,Real.rpow_natCast,div_eq_mul_inv] using hRep0
  have hSq0 := hSqL.2 Y Bs (3*L) hYone hLogY hBs hSqAmp (by positivity)
    (by simp only [Real.rpow_one]; exact le_rfl)
  have hSquare : square ≤ Budget := by
    simpa only [square,N,Budget,Real.rpow_natCast,div_eq_mul_inv] using hSq0
  let energy : ℝ := ∫ beta in Set.Icc (-(1/H)) (1/H),
    ‖sourceWeightedFullMarkedFourier Ncap qBase S Ts Tb q0 Vs Vsmall Vbig
      ts tb coef k primeSlot Parity (sourceAlphaDyadicCut alpha lo hi) c
      chi0 sigma0 sigma1 (fun n => psi1 ((n:ℝ)/Y)*sourcePhase n v1)
      (((h:ℝ)/(den:ℝ)+(beta:ℝ):ℝ):AddCircle (1:ℝ))‖^2
  have hRawBound : cb^2*energy ≤ 2*(2*(K*(low+tail))+2*rep)+2*cb^2*squareRaw := by
    simpa only [energy,low,tail,rep,squareRaw,H,N,Bamp,mul_assoc] using hRaw
  rw [hSquareEq] at hRawBound
  have hSave := source_arc_four_budget434 energy low tail rep square cb K Budget Cl Ct
    hcb hK.le hLow hTail hRepBound hSquare hRawBound
  change energy ≤ Kout*Budget at hSave
  have hRadius : 1/H = L^Carc/Hprime := by
    dsimp only [H]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,one_mul]
  have hSet : {beta : ℝ | |beta| ≤ L^Carc/Hprime} =
      Set.Icc (-(L^Carc/Hprime)) (L^Carc/Hprime) := by
    ext beta; simp only [Set.mem_setOf_eq,Set.mem_Icc,abs_le]
  unfold SourceOriginalArcConclusion434
  rw [hSet,←hRadius]
  change energy ≤ Kout*Y*L^(-(target:ℝ))
  simpa only [Budget,Real.rpow_neg hLp.le,Real.rpow_natCast,mul_assoc] using hSave
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalComparisonData -/

section

open MeasureTheory Filter
open scoped BigOperators FourierTransform SchwartzMap ContDiff RealInnerProductSpace
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin

/-- Fixed SOURCE bounds only; no arc, energy, or correlation proposition. -/
structure SourceComparisonFixed434 where
  aexp : ℝ
  bexp : ℝ
  cexp : ℝ
  Carc : ℝ
  CZ : ℝ
  τ : ℝ
  η : ℝ
  Cχ : ℝ
  C0 : ℝ
  q0 : ℝ
  vmin : ℝ
  A : ℝ
  Cpsi : ℝ
  Kpsi : ℕ → ℝ
  tmax : ℕ
  ea : ℕ
  ec : ℕ
  s0 : ℕ
  cm : ℕ
  s1base : ℕ
  vexp : ℕ
  fcut : ℕ
  epsi : ℕ
  hA : 1 ≤ A
  hCpsi : 0 ≤ Cpsi
  hKpsi : ∀ j, 0 ≤ Kpsi j
  hepsi : 3*Cpsi ≤ (epsi:ℝ)
  hFcut : Cpsi+2 < (fcut:ℝ)
  haexp : 0 < aexp
  hab : aexp < bexp
  hb : bexp < 1
  hbc : bexp < cexp
  hτ : 0 < τ
  hτη : τ < η
  hη : η < 1/4
  hCχ : 0 < Cχ
  hC0 : 0 ≤ C0
  hCarc : 0 ≤ Carc
  hq0 : 0 < q0
  hq1 : q0 < 1
  hv : 0 < vmin
  hcmChar : (cm:ℝ) ≤ Cχ
  hcmArc : (cm:ℝ) ≤ Carc

/-- Actual endpoint data and source admissibility. The discrepancy on alpha
is deliberately NOT a field: it is required at the first endpoint only. -/
structure SourceComparisonData434 (ι β : Type) [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β] (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ) where
  Z : ℝ
  hY : 4 ≤ Y
  hYmax : Y ≤ Real.exp (3*L/2)
  hH : 0 < Hprime
  hYstrong : Real.exp (3*L/4) ≤ Y
  hZ : x*L^(-cfg.CZ) ≤ Z
  hYIdent : Y = Z*Hprime
  hSmallGroups : (Fintype.card ι:ℝ) ≤ cfg.C0*Real.log L
  hBigGroups : (Fintype.card β:ℝ) ≤ cfg.C0*Real.log L
  lo : ℕ
  hi : ℕ
  Ncap : ℕ
  alpha : ℕ → ℂ
  hNcap : (Ncap:ℝ) ≤ x^2
  hCap : cfg.A*Y ≤ (Ncap:ℝ)
  hAlpha : ∀ m ∈ Finset.Icc lo hi, ‖alpha m‖ ≤ L^cfg.ea
  G : Finset ℕ
  Ptw : Finset ℕ
  S : Finset ℕ
  primeSlot : Finset ℕ
  Ts : ι → Finset ℕ
  Tb : β → Finset ℕ
  Vs : ℝ
  Vsmall : ι → ℝ
  Vbig : β → ℝ
  ts : ι → ℕ
  tb : β → ℕ
  coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ
  k : ℕ
  qBase : ℕ
  c : ℕ → ℂ
  chi0 : DirichletCharacter ℂ qBase
  hBase : 0 < qBase
  hBaseCap : (qBase:ℝ) ≤ L^cfg.cm
  hk : k+1 ≤ cfg.tmax
  hVs : cfg.vmin ≤ Vs
  hts : ∀ j, ts j ≤ cfg.tmax
  htb : ∀ j, tb j ≤ cfg.tmax
  hVsmall : ∀ j, cfg.vmin ≤ Vsmall j
  hVbig : ∀ j, cfg.vmin ≤ Vbig j
  hcoef : ∀ lists, ‖coef lists‖ ≤ 1
  C : ℝ
  hC : 0 ≤ C
  hCBudget : C ≤ L^cfg.ec
  hcBound : ∀ n, ‖c n‖ ≤ C
  sigma0 : ℝ
  sigma1 : ℝ
  hSigma0 : |sigma0| ≤ L^cfg.s0
  hSigma1 : |sigma1| ≤ L^cfg.s1base
  hModScale : L^(2*cfg.cm) ≤ Real.exp (Real.sqrt L)
  hSG : S ⊆ G
  hSPrime : ∀ v ∈ S, v.Prime
  hSN : ∀ v ∈ S, v ≤ Ncap
  hPN : ∀ p ∈ primeSlot, p ≤ Ncap
  hRough : ∀ m, sourceAlphaDyadicCut alpha lo hi m ≠ 0 →
    SourceRoughAbove m (Real.exp (Real.sqrt L))
  hGroup : ∀ v ∈ G, (v:ℝ) ≤ Real.exp (Real.sqrt L)
  hLong : ∀ p ∈ primeSlot, Real.exp (Real.sqrt L) < (p:ℝ)
  I : Set ℝ
  hI : Set.OrdConnected I
  hSmall : ∀ s ∈ S, Real.exp (L^cfg.aexp) ≤ (s:ℝ) ∧
    (s:ℝ) ≤ Real.exp (L^cfg.bexp)
  hSlot : ∀ p, p ∈ primeSlot ↔ p.Prime ∧ (p:ℝ) ∈ I
  hIBand : I ⊆ Set.Icc (x^cfg.τ) (x^cfg.η)
  F1 : Finset ℕ
  F2 : Finset ℕ
  p1 : ℕ → ℕ
  p2 : ℕ → ℕ
  U1 : ℝ
  U2 : ℝ
  hF1 : F1.Nonempty
  hF2 : F2.Nonempty
  hp1 : ∀ i ∈ F1, 1 ≤ p1 i
  hp2 : ∀ i ∈ F2, 1 ≤ p2 i
  hmin1 : ∀ i ∈ F1, Real.exp (L^cfg.cexp) ≤ (p1 i:ℝ)
  hmin2 : ∀ i ∈ F2, Real.exp (L^cfg.cexp) ≤ (p2 i:ℝ)
  hU1 : 0 < U1
  hU2 : 0 < U2
  hcell1 : Real.log (((∏ i ∈ F1, p1 i : ℕ):ℝ)) ≤ Real.log U1+1
  hcell2 : Real.log (((∏ i ∈ F2, p2 i : ℕ):ℝ)) ≤ Real.log U2+1
  hHIdent : Hprime = U1*U2
  psi1 : ℝ → ℂ
  hSmooth : ContDiff ℝ ∞ psi1
  hSupport : ∀ u, psi1 u ≠ 0 → 1/cfg.A ≤ u ∧ u ≤ cfg.A
  v1 : ℝ
  hv1 : |v1| ≤ L^cfg.vexp
  hBudget : sourceLogDerivativeBudget cfg.Cpsi cfg.Kpsi L (fun u => psi1 (Real.exp u))
  hG : G = S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
    ((Finset.univ : Finset β).biUnion Tb)
  hParity : Ptw ⊆ G
  hTsPrime : ∀ g, ∀ p ∈ Ts g, p.Prime
  hTbPrime : ∀ g, ∀ p ∈ Tb g, p.Prime
  hOrigW : L^cfg.Carc ≤ Real.exp (Real.sqrt L)
  hOrigSmall : L^cfg.Carc < Real.exp (L^cfg.aexp)
  hOrigLong : L^cfg.Carc < Real.exp (cfg.τ*L)
  hSlotMin : ∀ p ∈ primeSlot, Real.exp (cfg.τ*L) ≤ (p:ℝ)
  hHband : 2 ≤ Hprime/L^cfg.Carc
  hArcCap : Hprime/L^cfg.Carc ≤ Y/(8*cfg.A)
  hDisjS : ∀ g, ∀ p ∈ S, p ∉ Ts g
  hDisjB : ∀ g, ∀ p ∈ S, p ∉ Tb g

namespace SourceComparisonData434
variable {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
variable {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
noncomputable def alphaCut (d : SourceComparisonData434 ι β cfg x L Y Hprime) :=
  sourceAlphaDyadicCut d.alpha d.lo d.hi
noncomputable def cutoff (d : SourceComparisonData434 ι β cfg x L Y Hprime) (n : ℕ) : ℂ :=
  d.psi1 ((n:ℝ)/Y)*sourcePhase n d.v1
noncomputable def endpoint (d : SourceComparisonData434 ι β cfg x L Y Hprime) : ℤ → ℂ :=
  sourceOriginalFullEndpointCoefficients434 d.qBase d.S d.Ts d.Tb cfg.q0 d.Vs d.Vsmall d.Vbig
    d.ts d.tb d.coef d.k d.primeSlot d.alphaCut d.c d.chi0 d.sigma0 d.sigma1 d.cutoff
noncomputable def support (d : SourceComparisonData434 ι β cfg x L Y Hprime) : Finset ℤ :=
  (Finset.Icc 1 d.Ncap).image (fun n : ℕ => (n:ℤ))
end SourceComparisonData434
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryUnmarkedCoreMoment -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The genuine original prime-slot core alone has an L2 divisor
moment without marked endpoints, as needed after w=p*y.
No discrepancy, no weight at p*y and no false pointwise uniform cap. -/
theorem source_original_unmarked_core_global_square434
    (G primeSlot : Finset ℕ) (alpha c : ℕ → ℂ)
    (N q : ℕ) (chi : DirichletCharacter ℂ q)
    (s0 s1 A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hAlpha : ∀ m, ‖alpha m‖ ≤ A)
    (hCseq : ∀ r, ‖c r‖ ≤ C) :
    (∑ n ∈ Finset.Icc 1 N,
      ‖sourceCore (sourceOutsidePart G n)
        primeSlot alpha c q chi s0 s1‖^2) ≤
      (A*C)^2*(N:ℝ)*(1+Real.log (N:ℝ))^16 := by
  have h := source_original_endpoint_global_square434 G
    (fun _ => (1:ℂ)) (fun _ => (1:ℂ)) (fun _ => (1:ℂ))
    primeSlot alpha c N q chi s0 s1 A C 1 1
    hA hC (by norm_num) (by norm_num)
    hAlpha hCseq (fun _ _ => by norm_num)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num)
  simpa only [sourceEndpoint,mul_one,one_mul] using h

/-- Actual coefficients of an original C endpoint satisfy the
unmarked core L2 bound at ANY finite positive natural cap. -/
theorem source_data_unmarked_core_global_square434
    (cfg : SourceComparisonFixed434)
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x L Y Hprime : ℝ) (hL : 1 ≤ L)
    (u : SourceComparisonData434 ι β cfg x L Y Hprime) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
      ‖sourceCore (sourceOutsidePart u.G n)
        u.primeSlot u.alphaCut u.c u.qBase u.chi0 u.sigma0 u.sigma1‖^2) ≤
      (L^cfg.ea*L^cfg.ec)^2*(N:ℝ)*(1+Real.log (N:ℝ))^16 := by
  have hA : 0 ≤ L^cfg.ea := by positivity
  have hC : 0 ≤ L^cfg.ec := by positivity
  have hAlpha : ∀ m, ‖u.alphaCut m‖ ≤ L^cfg.ea := by
    intro m
    by_cases hm : m ∈ Finset.Icc u.lo u.hi
    · simpa [SourceComparisonData434.alphaCut,sourceAlphaDyadicCut,hm]
        using u.hAlpha m hm
    · simp only [SourceComparisonData434.alphaCut,
        sourceAlphaDyadicCut,if_neg hm,norm_zero]
      exact hA
  have hc (r : ℕ) : ‖u.c r‖ ≤ L^cfg.ec :=
    (u.hcBound r).trans u.hCBudget
  exact source_original_unmarked_core_global_square434
    u.G u.primeSlot u.alphaCut u.c N u.qBase u.chi0
    u.sigma0 u.sigma1 (L^cfg.ea) (L^cfg.ec)
    hA hC hAlpha hc
end Green64Analytic.CorrelationSquare

end

/-! ## SourceD61RoughModTwo -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64ComparisonPartial
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Literal SourceRoughAbove m W, when W>=2, forces odd parity.
The actual source W=exp(sqrt L) satisfies this eventually. -/
theorem source_rough_cofactor_odd434
    (m : ℕ) (W : ℝ)
    (hW : 2 ≤ W) (hm : SourceRoughAbove m W) : Odd m := by
  apply Nat.not_even_iff_odd.mp
  intro he
  have htwo : 2 ∣ m := even_iff_two_dvd.mp he
  have hlarge := hm 2 Nat.prime_two htwo
  have hreal : W < (2:ℝ) := by simpa using hlarge
  exact (not_lt_of_ge hW) hreal
/-- The q=|k|=2 residue constraint is automatic for the actual W-rough
cofactor support of both endpoints. Thus the residue-only Gram is exactly
the unrestricted complex Gram minus the integer-ratio diagonal; no
CRT saving is available at k=±2 from congruence alone. -/
theorem source_rough_q_two_residue_gram_exact434
    {ι : Type} (S : Finset ι)
    (m t : ι → ℕ) (B : ι → ℂ) (W : ℝ)
    (hW : 2 ≤ W)
    (hm : ∀ i ∈ S, SourceRoughAbove (m i) W)
    (ht : ∀ i ∈ S, SourceRoughAbove (t i) W) :
    (∑ i ∈ S, ∑ j ∈ S,
      if (2:ℤ) ∣ ((m i:ℤ)*(t j:ℤ) - (m j:ℤ)*(t i:ℤ)) ∧
          (m i:ℤ)*(t j:ℤ) ≠ (m j:ℤ)*(t i:ℤ)
      then B i * star (B j) else 0) =
      (∑ i ∈ S, B i) * star (∑ i ∈ S, B i) -
      ∑ i ∈ S, ∑ j ∈ S,
        if (m i:ℤ)*(t j:ℤ) = (m j:ℤ)*(t i:ℤ)
        then B i * star (B j) else 0 := by
  have hoddM : ∀ i ∈ S, Odd ((m i:ℕ):ℤ) := by
    intro i hi
    exact_mod_cast source_rough_cofactor_odd434 (m i) W hW (hm i hi)
  have hoddT : ∀ i ∈ S, Odd ((t i:ℕ):ℤ) := by
    intro i hi
    exact_mod_cast source_rough_cofactor_odd434 (t i) W hW (ht i hi)
  exact q_two_residue_gram_exact434 S
    (fun i => (m i:ℤ)) (fun i => (t i:ℤ)) B hoddM hoddT
end Green64ComparisonPartial

end

end

/-! ## SourceD61ActualQTwoGram -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64ComparisonPartial
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 3500000

/-- Exact native q=|k| and graph shift 2*k for the two smallest
nonzero even signed k values, with no orientation change. -/
theorem original_signed_small_k_modulus_shift434
    (k : ℤ) (hk : k = 2 ∨ k = -2) :
    k.natAbs = 2 ∧ (2*k=4 ∨ 2*k=-4) := by
  rcases hk with rfl | rfl
  · norm_num
  · norm_num

/-- Original W=exp(sqrt L) contains 2 for all sufficiently large L. -/
theorem eventually_original_W_above_two434 :
    ∀ᶠ L : ℝ in atTop, (2:ℝ) ≤ Real.exp (Real.sqrt L) := by
  filter_upwards [eventually_ge_atTop (1:ℝ)] with L hL
  have hs : 1 ≤ Real.sqrt L := Real.one_le_sqrt.mpr hL
  have he := Real.add_one_le_exp (Real.sqrt L)
  linarith
/-- At both literal signed k=±2, the exact source rough cofactor
support makes the mod-q congruence automatic; the remaining
residue-only signed Gram is an unrestricted off-integer-diagonal
complex double sum, not an automatically small error. -/
theorem eventually_actual_D61_small_k_residue_gram434 :
    ∀ᶠ L : ℝ in atTop,
    ∀ k : ℤ, (k = 2 ∨ k = -2) →
    ∀ {ι : Type} (S : Finset ι)
      (m t : ι → ℕ) (B : ι → ℂ),
      (∀ i ∈ S, SourceRoughAbove (m i) (Real.exp (Real.sqrt L))) →
      (∀ i ∈ S, SourceRoughAbove (t i) (Real.exp (Real.sqrt L))) →
      k.natAbs = 2 ∧
      ((2*k=4) ∨ (2*k=-4)) ∧
      (∑ i ∈ S, ∑ j ∈ S,
        if (k.natAbs:ℤ) ∣ ((m i:ℤ)*(t j:ℤ) - (m j:ℤ)*(t i:ℤ)) ∧
            (m i:ℤ)*(t j:ℤ) ≠ (m j:ℤ)*(t i:ℤ)
        then B i * star (B j) else 0) =
        (∑ i ∈ S, B i) * star (∑ i ∈ S, B i) -
        ∑ i ∈ S, ∑ j ∈ S,
          if (m i:ℤ)*(t j:ℤ) = (m j:ℤ)*(t i:ℤ)
          then B i * star (B j) else 0 := by
  filter_upwards [eventually_original_W_above_two434] with L hW
  intro k hk ι S m t B hm ht
  have hk2 := original_signed_small_k_modulus_shift434 k hk
  refine ⟨hk2.1, hk2.2, ?_⟩
  rw [hk2.1]
  exact source_rough_q_two_residue_gram_exact434
    S m t B (Real.exp (Real.sqrt L)) hW hm ht
end Green64ComparisonPartial

end

end

/-! ## SourceD61D20RoughSupport -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64ComparisonPartial
open Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- Exact D20 minFac roughness is the source's prime-divisor
SourceRoughAbove predicate, including repeated prime powers. -/
theorem original_D20_rough_implies_original_source_rough434
    (n : ℕ) (W : ℝ) (hD20 : sourceD20Rough W n) :
    SourceRoughAbove n W := by
  intro p hp hpDiv
  have hmin : n.minFac ≤ p :=
    Nat.minFac_le_of_dvd hp.two_le hpDiv
  have hCast : (n.minFac:ℝ) ≤ (p:ℝ) := by exact_mod_cast hmin
  exact hD20.2.trans_le hCast

/-- The TRUE D20 FULL Delta (test minus cell proxy) has zero coefficient
outside the original W-rough support. No shortened-cell renormalization
or replacement by a purely rough test is used. -/
theorem original_D20_full_delta_support_SourceRoughAbove434
    (Δ W y : ℝ) (n : ℕ) (hWy : W ≤ y)
    (hNZ : sourceD20FullDelta Δ W y n ≠ 0) :
    SourceRoughAbove n W := by
  apply original_D20_rough_implies_original_source_rough434 n W
  by_contra hnot
  have hz := sourceD20_delta_support
    (sourceD20LogCell Δ (sourceD20CellIndex Δ n)) hWy n hnot
  have heq : sourceD20FullDelta Δ W y n =
      sourceD20CellDelta
        (sourceD20LogCell Δ (sourceD20CellIndex Δ n)) W y n := rfl
  exact hNZ (heq.trans hz)

/-- Keep the unchanged FULL logarithmic cell; restrict only to
NONZERO D20 Delta coefficients, which preserves every original
signed sum and excludes all zero-support nonrough integers. -/
noncomputable def sourceD20ActiveFullCell434 (Δ W y : ℝ) (j : ℕ) :
    Finset ℕ :=
  (sourceD20LogCell Δ j).filter
    (fun n => sourceD20FullDelta Δ W y n ≠ 0)

theorem source_D20_active_full_cell_rough434
    (Δ W y : ℝ) (hWy : W ≤ y) (j n : ℕ)
    (hn : n ∈ sourceD20ActiveFullCell434 Δ W y j) :
    SourceRoughAbove n W :=
  original_D20_full_delta_support_SourceRoughAbove434 Δ W y n hWy
    (Finset.mem_filter.mp hn).2

/-- Signed centering is inherited LITERALLY from the complete D20 cell,
as the zero Delta coefficients have simply been dropped. -/
theorem source_D20_active_full_delta_zero434
    (Δ W y : ℝ) (hΔ : 0 < Δ) (hWy : W ≤ y) (j : ℕ) :
    (∑ n ∈ sourceD20ActiveFullCell434 Δ W y j,
      sourceD20FullDelta Δ W y n) = 0 := by
  have hfull := sourceD20_full_delta_zero hΔ hWy j
  unfold sourceD20ActiveFullCell434
  rw [Finset.sum_filter]
  have heq :
      (∑ n ∈ sourceD20LogCell Δ j,
        if sourceD20FullDelta Δ W y n ≠ 0
        then sourceD20FullDelta Δ W y n else 0) =
      ∑ n ∈ sourceD20LogCell Δ j, sourceD20FullDelta Δ W y n := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hzero : sourceD20FullDelta Δ W y n = 0
    · simp [hzero]
    · simp [hzero]
  exact heq.trans hfull
end Green64ComparisonPartial

end

end

/-! ## SourceD20FullDeltaL2Exact -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64ComparisonPartial
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Exact L² energy of the ORIGINAL full-cell D20 centered coefficient:
A(B-A)/B, where A is the count of y-rough integers and B of W-rough
integers in the SAME unshortened cell. A/B=0 if B=0, with A=0 by support.

This is the literal original unweighted ratio, NOT a harmonic
recentering or shorter complementary-divisor fibre; it shows that the
signed D20 centering yields a positive variance on full cells. -/
theorem source_original_D20_full_cell_l2_exact434
    (Δ W y : ℝ) (hΔ : 0 < Δ) (hWy : W ≤ y) (j : ℕ) :
    let C := sourceD20LogCell Δ j
    let A : ℝ := ((C.filter (sourceD20Rough y)).card:ℝ)
    let B : ℝ := ((C.filter (sourceD20Rough W)).card:ℝ)
    (∑ n ∈ C, (sourceD20FullDelta Δ W y n)^2) =
      A*(B-A)/B := by
  classical
  let C := sourceD20LogCell Δ j
  let A : ℝ := ((C.filter (sourceD20Rough y)).card:ℝ)
  let B : ℝ := ((C.filter (sourceD20Rough W)).card:ℝ)
  let ρ : ℝ := sourceD20CellRatio C W y
  change (∑ n ∈ C, (sourceD20FullDelta Δ W y n)^2) = A*(B-A)/B
  have hSubset := sourceD20_selected_subset C hWy
  have hAB : A ≤ B := by
    dsimp [A,B]
    exact_mod_cast Finset.card_le_card hSubset
  have hT (v : ℝ) : ∑ n ∈ C, sourceD19RoughTest v n =
      ((C.filter (sourceD20Rough v)).card:ℝ) := by
    change (∑ n ∈ C,
      if 2 ≤ n ∧ v < (n.minFac:ℝ) then (1:ℝ) else 0) = _
    rw [Finset.sum_boole]
    have hEq : C.filter (fun n : ℕ => 2 ≤ n ∧ v < (n.minFac:ℝ)) =
        C.filter (sourceD20Rough v) := by
      ext n
      simp only [Finset.mem_filter, sourceD20Rough]
    rw [hEq]
  have hPoint (n : ℕ) (hn : n ∈ C) :
      (sourceD20FullDelta Δ W y n)^2 =
        sourceD19RoughTest y n -
        2*ρ*sourceD19RoughTest y n +
        ρ^2*sourceD19RoughTest W n := by
    rw [sourceD20FullDelta,sourceD20_full_proxy_on_cell hΔ hn]
    have hProxy : sourceD20CellProxy C W y n =
        (if sourceD20Rough W n then ρ else 0) := rfl
    rw [hProxy]
    dsimp only [sourceD19RoughTest]
    by_cases hy : 2 ≤ n ∧ y < (n.minFac:ℝ)
    · have hW : 2 ≤ n ∧ W < (n.minFac:ℝ) :=
        ⟨hy.1, lt_of_le_of_lt hWy hy.2⟩
      simp [hy,hW,ρ,sourceD20Rough] <;> ring
    · by_cases hW : 2 ≤ n ∧ W < (n.minFac:ℝ)
      · have hy' : ¬ y < (n.minFac:ℝ) := by
          intro hh
          exact hy ⟨hW.1, hh⟩
        simp [hy',hW,ρ,sourceD20Rough] <;> ring
      · simp [hy,hW,ρ,sourceD20Rough] <;> ring
  have hSum :
      (∑ n ∈ C, (sourceD20FullDelta Δ W y n)^2) =
        A - 2*ρ*A + ρ^2*B := by
    calc
      _ = ∑ n ∈ C,
          (sourceD19RoughTest y n -
            2*ρ*sourceD19RoughTest y n +
            ρ^2*sourceD19RoughTest W n) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact hPoint n hn
      _ = A - 2*ρ*A + ρ^2*B := by
        rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
        simp only [←Finset.mul_sum,hT]
        dsimp [A,B]
  by_cases hB : B = 0
  · have hA : A = 0 := by
      have hA0 : 0 ≤ A := by dsimp [A]; positivity
      linarith [hAB]
    have hRho : ρ = A/B := rfl
    rw [hSum,hRho,hA,hB]
    norm_num
  · have hRho : ρ = A/B := rfl
    rw [hSum,hRho]
    field_simp
    ring
end Green64ComparisonPartial

end

end

/-! ## D20ExactL1Mass -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64ComparisonPartial
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- Exact TOTAL ABSOLUTE MASS of the original unshortened D20
centered rough coefficient. Unlike an arbitrary signed sequence,
its two-valued original W/y-rough tests yield L1=2*L2^2:
  sum_C |Delta_n| = 2*A*(B-A)/B.
This sharp mass identity uses the SAME original cell ratios A/B,
retaining empty/zero-denominator boundary cells. No shortening to
the sparse complementary-divisor support or cardinality bound. -/
theorem green64_original_D20_full_cell_L1_exact434
    (Δ W y : ℝ) (hΔ : 0 < Δ) (hWy : W ≤ y) (j : ℕ) :
    let C := sourceD20LogCell Δ j;
    let A : ℝ := ((C.filter (sourceD20Rough y)).card:ℝ);
    let B : ℝ := ((C.filter (sourceD20Rough W)).card:ℝ);
    (∑ n ∈ C, |sourceD20FullDelta Δ W y n|) =
      2*A*(B-A)/B := by
  classical
  let C := sourceD20LogCell Δ j
  let A : ℝ := ((C.filter (sourceD20Rough y)).card:ℝ)
  let B : ℝ := ((C.filter (sourceD20Rough W)).card:ℝ)
  let ρ : ℝ := sourceD20CellRatio C W y
  change (∑ n ∈ C, |sourceD20FullDelta Δ W y n|) =
    2*A*(B-A)/B
  obtain ⟨hρ0,hρ1⟩ := sourceD20_ratio_bounds C hWy
  have hPoint (n : ℕ) (hn : n ∈ C) :
      |sourceD20FullDelta Δ W y n| =
        2*(1-ρ)*sourceD19RoughTest y n -
          sourceD20FullDelta Δ W y n := by
    rw [sourceD20FullDelta,sourceD20_full_proxy_on_cell hΔ hn]
    change |sourceD19RoughTest y n -
      (if sourceD20Rough W n then ρ else 0)| =
      2*(1-ρ)*sourceD19RoughTest y n -
        (sourceD19RoughTest y n -
         (if sourceD20Rough W n then ρ else 0))
    have hTest : sourceD19RoughTest y n =
        (if sourceD20Rough y n then (1:ℝ) else 0) := by
      by_cases hp : 2 ≤ n ∧ y < (n.minFac:ℝ)
      · simp [sourceD19RoughTest,sourceD20Rough,hp]
      · simp [sourceD19RoughTest,sourceD20Rough,hp]
    rw [hTest]
    by_cases hy : sourceD20Rough y n
    · have hW : sourceD20Rough W n := sourceD20_rough_mono hWy hy
      simp only [if_pos hy,if_pos hW]
      rw [abs_of_nonneg (sub_nonneg.mpr hρ1)]
      ring
    · by_cases hW : sourceD20Rough W n
      · simp only [if_neg hy,if_pos hW]
        rw [zero_sub,abs_neg,abs_of_nonneg hρ0]
        ring
      · simp only [if_neg hy,if_neg hW]
        ring
  have hT : (∑ n ∈ C, sourceD19RoughTest y n) = A := by
    change (∑ n ∈ C,
      if 2 ≤ n ∧ y < (n.minFac:ℝ) then (1:ℝ) else 0) = _
    rw [Finset.sum_boole]
    have hEq : C.filter (fun n : ℕ => 2 ≤ n ∧ y < (n.minFac:ℝ)) =
      C.filter (sourceD20Rough y) := by
      ext n
      simp only [Finset.mem_filter,sourceD20Rough]
    rw [hEq]
  have hSum : (∑ n ∈ C, |sourceD20FullDelta Δ W y n|) =
      2*(1-ρ)*A := by
    calc
      _ = ∑ n ∈ C, (2*(1-ρ)*sourceD19RoughTest y n -
          sourceD20FullDelta Δ W y n) :=
        Finset.sum_congr rfl hPoint
      _ = 2*(1-ρ)*A := by
        rw [Finset.sum_sub_distrib,← Finset.mul_sum,hT,
          sourceD20_full_delta_zero hΔ hWy j,sub_zero]
  have hAB : A ≤ B := by
    dsimp only [A,B]
    exact_mod_cast Finset.card_le_card
      (sourceD20_selected_subset C hWy)
  by_cases hB : B = 0
  · have hA : A = 0 := by
      have hA0 : 0 ≤ A := by dsimp [A]; positivity
      linarith
    rw [hSum,show ρ=A/B from rfl,hA,hB]
    norm_num
  · rw [hSum,show ρ=A/B from rfl]
    field_simp
end Green64ComparisonPartial

end

end

/-! ## SourceD20FullDeltaTensorL2 -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64ComparisonPartial
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- Full ORIGINAL D20 centered signed-pair tensor has EXACT factored
quadratic energy. Both D20 logarithmic cells are complete and the
unweighted proxy ratio is unmodified. This is NOT an assumption of
independent complementary-divisor fibres. -/
theorem source_original_D20_full_pair_l2_tensor434
    (Δ W y : ℝ) (hΔ : 0 < Δ) (hWy : W ≤ y) (j₁ j₂ : ℕ) :
    let C1 := sourceD20LogCell Δ j₁
    let C2 := sourceD20LogCell Δ j₂
    let A1 : ℝ := ((C1.filter (sourceD20Rough y)).card:ℝ)
    let B1 : ℝ := ((C1.filter (sourceD20Rough W)).card:ℝ)
    let A2 : ℝ := ((C2.filter (sourceD20Rough y)).card:ℝ)
    let B2 : ℝ := ((C2.filter (sourceD20Rough W)).card:ℝ)
    (∑ i ∈ C1.product C2,
      (sourceD20FullDelta Δ W y i.1 *
        sourceD20FullDelta Δ W y i.2)^2) =
      (A1*(B1-A1)/B1)*(A2*(B2-A2)/B2) := by
  classical
  let C1 := sourceD20LogCell Δ j₁
  let C2 := sourceD20LogCell Δ j₂
  let A1 : ℝ := ((C1.filter (sourceD20Rough y)).card:ℝ)
  let B1 : ℝ := ((C1.filter (sourceD20Rough W)).card:ℝ)
  let A2 : ℝ := ((C2.filter (sourceD20Rough y)).card:ℝ)
  let B2 : ℝ := ((C2.filter (sourceD20Rough W)).card:ℝ)
  have h1 : (∑ n ∈ C1,(sourceD20FullDelta Δ W y n)^2) =
      A1*(B1-A1)/B1 :=
    source_original_D20_full_cell_l2_exact434 Δ W y hΔ hWy j₁
  have h2 : (∑ n ∈ C2,(sourceD20FullDelta Δ W y n)^2) =
      A2*(B2-A2)/B2 :=
    source_original_D20_full_cell_l2_exact434 Δ W y hΔ hWy j₂
  change (∑ i ∈ C1.product C2,
      (sourceD20FullDelta Δ W y i.1 *
        sourceD20FullDelta Δ W y i.2)^2) =
      (A1*(B1-A1)/B1)*(A2*(B2-A2)/B2)
  calc
    _ = (∑ x ∈ C1,∑ z ∈ C2,
      (sourceD20FullDelta Δ W y x*
        sourceD20FullDelta Δ W y z)^2) :=
      Finset.sum_product C1 C2 (fun i : ℕ × ℕ =>
        (sourceD20FullDelta Δ W y i.1 *
          sourceD20FullDelta Δ W y i.2)^2)
    _ = ∑ x ∈ C1,(sourceD20FullDelta Δ W y x)^2*
        (∑ z ∈ C2,(sourceD20FullDelta Δ W y z)^2) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp_rw [mul_pow]
      rw [Finset.mul_sum]
    _ = (∑ x ∈ C1,(sourceD20FullDelta Δ W y x)^2)*
        (∑ z ∈ C2,(sourceD20FullDelta Δ W y z)^2) := by
      rw [Finset.sum_mul]
    _ = _ := by rw [h1,h2]
end Green64ComparisonPartial

end

end

/-! ## D20ExactTensorL1Mass -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64ComparisonPartial
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Sharp EXACT TOTAL ABSOLUTE signed mass of the two full original
D20 cells: 4 times the product of the original full D20 variances.
No sparse restriction re-centering and no cell-count loss. -/
theorem green64_original_D20_full_pair_L1_exact434
    (Δ W y : ℝ) (hΔ : 0 < Δ) (hWy : W ≤ y)
    (j₁ j₂ : ℕ) :
    let C1 := sourceD20LogCell Δ j₁;
    let C2 := sourceD20LogCell Δ j₂;
    let A1 : ℝ := ((C1.filter (sourceD20Rough y)).card:ℝ);
    let B1 : ℝ := ((C1.filter (sourceD20Rough W)).card:ℝ);
    let A2 : ℝ := ((C2.filter (sourceD20Rough y)).card:ℝ);
    let B2 : ℝ := ((C2.filter (sourceD20Rough W)).card:ℝ);
    (∑ i ∈ C1.product C2,
      |sourceD20FullDelta Δ W y i.1 *
       sourceD20FullDelta Δ W y i.2|) =
      4*(A1*(B1-A1)/B1)*(A2*(B2-A2)/B2) := by
  classical
  let C1 := sourceD20LogCell Δ j₁
  let C2 := sourceD20LogCell Δ j₂
  let A1 : ℝ := ((C1.filter (sourceD20Rough y)).card:ℝ)
  let B1 : ℝ := ((C1.filter (sourceD20Rough W)).card:ℝ)
  let A2 : ℝ := ((C2.filter (sourceD20Rough y)).card:ℝ)
  let B2 : ℝ := ((C2.filter (sourceD20Rough W)).card:ℝ)
  have hL1 := green64_original_D20_full_cell_L1_exact434
    Δ W y hΔ hWy j₁
  have hL2 := green64_original_D20_full_cell_L1_exact434
    Δ W y hΔ hWy j₂
  change (∑ i ∈ C1.product C2,
      |sourceD20FullDelta Δ W y i.1 *
       sourceD20FullDelta Δ W y i.2|) =
      4*(A1*(B1-A1)/B1)*(A2*(B2-A2)/B2)
  change (∑ m ∈ C1, |sourceD20FullDelta Δ W y m|) =
    2*A1*(B1-A1)/B1 at hL1
  change (∑ t ∈ C2, |sourceD20FullDelta Δ W y t|) =
    2*A2*(B2-A2)/B2 at hL2
  have hFubini :
      (∑ i ∈ C1.product C2,
        |sourceD20FullDelta Δ W y i.1 *
         sourceD20FullDelta Δ W y i.2|) =
      (∑ m ∈ C1, |sourceD20FullDelta Δ W y m|) *
        (∑ t ∈ C2, |sourceD20FullDelta Δ W y t|) := by
    change (∑ i ∈ C1 ×ˢ C2,
      |sourceD20FullDelta Δ W y i.1 *
       sourceD20FullDelta Δ W y i.2|) = _
    rw [Finset.sum_product,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro t ht
    rw [abs_mul]
  rw [hFubini,hL1,hL2]
  ring
end Green64ComparisonPartial

end

end

/-! ## SourceD61ProjectedQTwoResidue -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64ComparisonPartial
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- At the literal smallest signed original shifts k=±2, the q=|k|
character congruence is automatically satisfied by every two original
W-rough cofactors, even AFTER the mandatory FOUR-SIGN parity projector
is formed at each endpoint. Hence the exact off-integer-diagonal
projected complex Gram is the squared fully-signed four-channel sum
MINUS the integer-ratio diagonal. No off-diagonal positivity, saving,
or replacement by a sum of four unsigned energies is inferred. -/
theorem eventually_original_D61_projected_small_k_four_sign_gram434 :
    ∀ᶠ L : ℝ in atTop,
    ∀ k : ℤ, (k = 2 ∨ k = -2) →
    ∀ {ι : Type} (S : Finset ι)
      (m t : ι → ℕ) (B e₁ e₂ : ι → ℂ) (M : ℕ),
    (∀ i ∈ S, SourceRoughAbove (m i) (Real.exp (Real.sqrt L))) →
    (∀ i ∈ S, SourceRoughAbove (t i) (Real.exp (Real.sqrt L))) →
    k.natAbs = 2 ∧ (2*k=4 ∨ 2*k=-4) ∧
    (∑ i ∈ S, ∑ j ∈ S,
       if (k.natAbs:ℤ) ∣
            ((m i:ℤ)*(t j:ℤ) - (m j:ℤ)*(t i:ℤ)) ∧
           (m i:ℤ)*(t j:ℤ) ≠ (m j:ℤ)*(t i:ℤ)
       then (B i*originalD61ParityProjector434 M (e₁ i)*
            originalD61ParityProjector434 M (e₂ i)) *
         star (B j*originalD61ParityProjector434 M (e₁ j)*
            originalD61ParityProjector434 M (e₂ j))
       else 0) =
     ((1/4:ℂ)*((∑ i ∈ S, B i) -
         (-1:ℂ)^M*(∑ i ∈ S, B i*e₁ i) -
         (-1:ℂ)^M*(∑ i ∈ S, B i*e₂ i) +
         (∑ i ∈ S, B i*e₁ i*e₂ i))) *
     star ((1/4:ℂ)*((∑ i ∈ S, B i) -
         (-1:ℂ)^M*(∑ i ∈ S, B i*e₁ i) -
         (-1:ℂ)^M*(∑ i ∈ S, B i*e₂ i) +
         (∑ i ∈ S, B i*e₁ i*e₂ i))) -
     ∑ i ∈ S, ∑ j ∈ S,
       if (m i:ℤ)*(t j:ℤ) = (m j:ℤ)*(t i:ℤ)
       then (B i*originalD61ParityProjector434 M (e₁ i)*
            originalD61ParityProjector434 M (e₂ i)) *
         star (B j*originalD61ParityProjector434 M (e₁ j)*
            originalD61ParityProjector434 M (e₂ j))
       else 0 := by
  classical
  filter_upwards [eventually_original_W_above_two434] with L hW
  intro k hk ι S m t B e₁ e₂ M hm ht
  have hSign := original_signed_small_k_modulus_shift434 k hk
  refine ⟨hSign.1,hSign.2,?_⟩
  rw [hSign.1]
  let Bproj : ι → ℂ := fun i =>
    B i*originalD61ParityProjector434 M (e₁ i)*
      originalD61ParityProjector434 M (e₂ i)
  have hR := source_rough_q_two_residue_gram_exact434
    S m t Bproj (Real.exp (Real.sqrt L)) hW hm ht
  have hFour := original_D61_four_sign_linear_sum434 S M e₁ e₂ B
  change
    (∑ i ∈ S, ∑ j ∈ S,
       if (2:ℤ) ∣ ((m i:ℤ)*(t j:ℤ)-(m j:ℤ)*(t i:ℤ)) ∧
        (m i:ℤ)*(t j:ℤ) ≠ (m j:ℤ)*(t i:ℤ)
       then Bproj i * star (Bproj j) else 0) = _
  rw [hR, hFour]
end Green64ComparisonPartial

end

end

/-! ## SourceD61ProjectedQTwoFibres -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64ComparisonPartial
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- The original signed k=±2 projected Gram admits an EXACT decomposition
into the squared four-sign total and rational-slope-fibre squares. The latter
keep all cross terms with the same m/t ratio. The source W-roughness itself
forces positive t_i, so no separate positivity is inserted. -/
theorem eventually_original_D61_projected_qtwo_rational_fibres434 :
    ∀ᶠ L : ℝ in atTop,
    ∀ k : ℤ, (k=2 ∨ k= -2) →
    ∀ {ι : Type} (S : Finset ι) (m t : ι → ℕ)
      (B e₁ e₂ : ι → ℂ) (M : ℕ),
    (∀ i ∈ S, SourceRoughAbove (m i) (Real.exp (Real.sqrt L))) →
    (∀ i ∈ S, SourceRoughAbove (t i) (Real.exp (Real.sqrt L))) →
    let Bp : ι → ℂ := fun i =>
      B i*originalD61ParityProjector434 M (e₁ i)*
        originalD61ParityProjector434 M (e₂ i)
    let four : ℂ := (1/4:ℂ)*((∑ i ∈ S, B i) -
      (-1:ℂ)^M*(∑ i ∈ S, B i*e₁ i) -
      (-1:ℂ)^M*(∑ i ∈ S, B i*e₂ i) +
      (∑ i ∈ S, B i*e₁ i*e₂ i))
    k.natAbs=2 ∧ (2*k=4 ∨ 2*k= -4) ∧
    (∑ i ∈ S, ∑ j ∈ S,
      if (k.natAbs:ℤ) ∣
          ((m i:ℤ)*(t j:ℤ)-(m j:ℤ)*(t i:ℤ)) ∧
         (m i:ℤ)*(t j:ℤ) ≠ (m j:ℤ)*(t i:ℤ)
      then Bp i * star (Bp j) else 0) =
      four * star four -
      ∑ q ∈ S.image (fun i => (m i:ℚ)/(t i:ℚ)),
        (∑ i ∈ S.filter (fun i => (m i:ℚ)/(t i:ℚ)=q), Bp i) *
        star (∑ j ∈ S.filter (fun j => (m j:ℚ)/(t j:ℚ)=q), Bp j) := by
  classical
  filter_upwards [eventually_original_D61_projected_small_k_four_sign_gram434,
    eventually_original_W_above_two434] with L hOriginal hW
  intro k hk ι S m t B e₁ e₂ M hm ht
  obtain ⟨hk2,hshift,hEq⟩ := hOriginal k hk S m t B e₁ e₂ M hm ht
  have htPos : ∀ i ∈ S, 0 < t i := by
    intro i hi
    obtain ⟨n, hn⟩ := source_rough_cofactor_odd434 (t i)
      (Real.exp (Real.sqrt L)) hW (ht i hi)
    omega
  dsimp only
  refine ⟨hk2,hshift,?_⟩
  let Bp : ι → ℂ := fun i =>
    B i*originalD61ParityProjector434 M (e₁ i)*
      originalD61ParityProjector434 M (e₂ i)
  have hDiag := integer_ratio_complex_diagonal_fibres434
    S m t Bp htPos
  rw [hEq, hDiag]

/-- A useful ONE-SIDED fact about the smallest physical character
moduli: the negative real part of the signed off-diagonal residue
Gram can be bounded by the exact rational-ratio diagonal energy,
without dropping four-sign cross channels. This is not yet the
whole source comparison integral or a bound on that diagonal. -/
theorem eventually_original_D61_qtwo_projected_negative_part434 :
    ∀ᶠ L : ℝ in atTop,
    ∀ k : ℤ, (k=2 ∨ k= -2) →
    ∀ {ι : Type} (S : Finset ι) (m t : ι → ℕ)
      (B e₁ e₂ : ι → ℂ) (M : ℕ),
    (∀ i ∈ S, SourceRoughAbove (m i) (Real.exp (Real.sqrt L))) →
    (∀ i ∈ S, SourceRoughAbove (t i) (Real.exp (Real.sqrt L))) →
    let Bp : ι → ℂ := fun i =>
      B i*originalD61ParityProjector434 M (e₁ i)*
        originalD61ParityProjector434 M (e₂ i)
    (- (∑ i ∈ S, ∑ j ∈ S,
      if (k.natAbs:ℤ) ∣
          ((m i:ℤ)*(t j:ℤ)-(m j:ℤ)*(t i:ℤ)) ∧
         (m i:ℤ)*(t j:ℤ) ≠ (m j:ℤ)*(t i:ℤ)
      then Bp i * star (Bp j) else 0).re) ≤
      (∑ q ∈ S.image (fun i => (m i:ℚ)/(t i:ℚ)),
        (∑ i ∈ S.filter (fun i => (m i:ℚ)/(t i:ℚ)=q), Bp i) *
        star (∑ j ∈ S.filter (fun j => (m j:ℚ)/(t j:ℚ)=q), Bp j)).re := by
  classical
  filter_upwards [eventually_original_D61_projected_qtwo_rational_fibres434]
    with L hFib
  intro k hk ι S m t B e₁ e₂ M hm ht
  obtain ⟨_,_,hEq⟩ := hFib k hk S m t B e₁ e₂ M hm ht
  dsimp only
  rw [hEq]
  have hpos :
      0 ≤ ((1/4:ℂ)*((∑ i ∈ S, B i) -
      (-1:ℂ)^M*(∑ i ∈ S, B i*e₁ i) -
      (-1:ℂ)^M*(∑ i ∈ S, B i*e₂ i) +
      (∑ i ∈ S, B i*e₁ i*e₂ i)) *
      star ((1/4:ℂ)*((∑ i ∈ S, B i) -
      (-1:ℂ)^M*(∑ i ∈ S, B i*e₁ i) -
      (-1:ℂ)^M*(∑ i ∈ S, B i*e₂ i) +
      (∑ i ∈ S, B i*e₁ i*e₂ i)))).re := by
    let z : ℂ := (1/4:ℂ)*((∑ i ∈ S, B i) -
      (-1:ℂ)^M*(∑ i ∈ S, B i*e₁ i) -
      (-1:ℂ)^M*(∑ i ∈ S, B i*e₂ i) +
      (∑ i ∈ S, B i*e₁ i*e₂ i))
    change 0 ≤ (z * (starRingEnd ℂ) z).re
    rw [Complex.mul_conj]
    exact Complex.normSq_nonneg z
  simp only [Complex.sub_re, Complex.neg_re]
  linarith
end Green64ComparisonPartial

end

end

/-! ## SourceD61FullD20ProjectedQTwo -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64ComparisonPartial
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Complete ORIGINAL D20 logarithmic-cell pair, restricted only to
NONZERO weights. This restriction changes neither the full signed
D20 sum nor its centering. It is not a shortened-residue cofactor
fibre and does not renormalize the D20 proxy. -/
noncomputable def sourceD20ActiveFullPair434 (Δ W y : ℝ)
    (j₁ j₂ : ℕ) : Finset (ℕ × ℕ) :=
  (sourceD20ActiveFullCell434 Δ W y j₁) ×ˢ
  (sourceD20ActiveFullCell434 Δ W y j₂)

/-- Literal signed full D20 Delta pair coefficient, with the full
physical kernel H left complex and otherwise unrestricted. -/
noncomputable def sourceD20FullPairCoefficient434
    (Δ W y : ℝ) (H : ℕ → ℕ → ℂ) (i : ℕ × ℕ) : ℂ :=
  (sourceD20FullDelta Δ W y i.1 : ℂ) *
  (sourceD20FullDelta Δ W y i.2 : ℂ) * H i.1 i.2

/-- The exact true FULL-CELL D20 signed coefficient supports the
original q=|k|=2 off-integer-diagonal four-sign Gram identity and its
one-sided negative-part bound. ALL H (including native K, the two
Fourier measures and actual cofactor masks) remain inside a complex
kernel; this theorem does NOT estimate that kernel or prove an
identity to the full D61 comparison-integral. -/
theorem eventually_source_D61_FULL_D20_qtwo_negative_part434 :
    ∀ᶠ L : ℝ in atTop,
    ∀ (Δ y : ℝ) (j₁ j₂ : ℕ) (k : ℤ)
      (H : ℕ → ℕ → ℂ)
      (e₁ e₂ : (ℕ × ℕ) → ℂ) (M : ℕ),
      Real.exp (Real.sqrt L) ≤ y →
      (k=2 ∨ k= -2) →
      let W := Real.exp (Real.sqrt L)
      let S := sourceD20ActiveFullPair434 Δ W y j₁ j₂
      let B := sourceD20FullPairCoefficient434 Δ W y H
      let Bp : (ℕ × ℕ) → ℂ := fun i =>
        B i * originalD61ParityProjector434 M (e₁ i) *
        originalD61ParityProjector434 M (e₂ i)
      (- (∑ i ∈ S, ∑ j ∈ S,
        if (k.natAbs:ℤ) ∣
             ((i.1:ℤ)*(j.2:ℤ)-(j.1:ℤ)*(i.2:ℤ)) ∧
           (i.1:ℤ)*(j.2:ℤ) ≠ (j.1:ℤ)*(i.2:ℤ)
        then Bp i * star (Bp j) else 0).re) ≤
        (∑ q ∈ S.image (fun i => (i.1:ℚ)/(i.2:ℚ)),
          (∑ i ∈ S.filter (fun i => (i.1:ℚ)/(i.2:ℚ)=q), Bp i) *
          star (∑ j ∈ S.filter (fun j => (j.1:ℚ)/(j.2:ℚ)=q), Bp j)).re := by
  classical
  filter_upwards [eventually_original_D61_qtwo_projected_negative_part434]
    with L hQ
  intro Δ y j₁ j₂ k H e₁ e₂ M hWy hk
  let W := Real.exp (Real.sqrt L)
  let S := sourceD20ActiveFullPair434 Δ W y j₁ j₂
  let B := sourceD20FullPairCoefficient434 Δ W y H
  have hm : ∀ i ∈ S, Green64Analytic.CorrelationD.SourceRoughAbove
      i.1 W := by
    intro i hi
    exact source_D20_active_full_cell_rough434 Δ W y hWy j₁ i.1
      (Finset.mem_product.mp hi).1
  have ht : ∀ i ∈ S, Green64Analytic.CorrelationD.SourceRoughAbove
      i.2 W := by
    intro i hi
    exact source_D20_active_full_cell_rough434 Δ W y hWy j₂ i.2
      (Finset.mem_product.mp hi).2
  exact hQ k hk S (fun i => i.1) (fun i => i.2) B e₁ e₂ M hm ht
end Green64ComparisonPartial

end

end

/-! ## SourceD61MaskedOriginalFullCellMixed -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64ComparisonPartial
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- EXACT original D20 full-cell signed centering over an ARBITRARY
sparse complementary-divisor support S. The whole pair H must
first be extended by ZERO off S, retaining all masks, characters,
Ptw projectors, signed 2k and source D before centering. The
projection to S is NOT itself centered. For every true D20 cell
pair, the coherent signed sum on S equals the FULL-CELL mixed
difference of the zero-extended physical source kernel.

No regularity/smallness is assumed or derived. In particular,
a sharp short complementary-fibre support S can make the mixed
difference as large as H itself: full-cell centering alone
does NOT give the required D61 log saving. -/
theorem source_original_D20_sparse_mask_full_cell_mixed434
    (Δ W y : ℝ) (hΔ : 0 < Δ) (hWy : W ≤ y)
    (j₁ j₂ : ℕ) (S : Finset (ℕ × ℕ))
    (hS : S ⊆ (sourceD20LogCell Δ j₁).product
      (sourceD20LogCell Δ j₂))
    (H : ℕ × ℕ → ℂ) (m₀ t₀ : ℕ) :
    let K : ℕ → ℕ → ℂ := fun m t =>
      if (m,t)∈S then H (m,t) else 0
    (∑ i ∈ S,
        ((sourceD20FullDelta Δ W y i.1:ℝ):ℂ)*
        ((sourceD20FullDelta Δ W y i.2:ℝ):ℂ)*H i) =
    ∑ m ∈ sourceD20LogCell Δ j₁,
      ∑ t ∈ sourceD20LogCell Δ j₂,
        ((sourceD20FullDelta Δ W y m:ℝ):ℂ)*
        ((sourceD20FullDelta Δ W y t:ℝ):ℂ)*
          (K m t-K m t₀-K m₀ t+K m₀ t₀) := by
  classical
  let C1 := sourceD20LogCell Δ j₁
  let C2 := sourceD20LogCell Δ j₂
  let δ := sourceD20FullDelta Δ W y
  let K : ℕ → ℕ → ℂ := fun m t =>
    if (m,t)∈S then H (m,t) else 0
  change (∑ i ∈ S, (δ i.1:ℂ)*(δ i.2:ℂ)*H i) =
    ∑ m ∈ C1,∑ t ∈ C2,
      (δ m:ℂ)*(δ t:ℂ)*
        (K m t-K m t₀-K m₀ t+K m₀ t₀)
  have hCell := source_D20_full_cell_complex_mixed_difference434
    Δ W y hΔ hWy j₁ j₂ m₀ t₀ K
  have hExpand : (∑ m ∈ C1,∑ t ∈ C2,
      (δ m:ℂ)*(δ t:ℂ)*K m t) =
      ∑ i ∈ C1.product C2,
      (δ i.1:ℂ)*(δ i.2:ℂ)*K i.1 i.2 := by
    exact (Finset.sum_product C1 C2
      (fun i : ℕ×ℕ => (δ i.1:ℂ)*(δ i.2:ℂ)*K i.1 i.2)).symm
  have hExtend : (∑ i ∈ C1.product C2,
      (δ i.1:ℂ)*(δ i.2:ℂ)*K i.1 i.2) =
      ∑ i ∈ S,(δ i.1:ℂ)*(δ i.2:ℂ)*H i := by
    calc
      _ = ∑ i ∈ S, (δ i.1:ℂ)*(δ i.2:ℂ)*K i.1 i.2 := by
        apply (Finset.sum_subset hS _).symm
        intro i hi hiS
        dsimp [K]
        simp only [if_neg hiS, mul_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [K,hi]
  rw [hExpand,hExtend] at hCell
  exact hCell
end Green64ComparisonPartial

end

end

/-! ## SourceD61ProjectedSparseMaskedMixed -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64ComparisonPartial
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- The EXACT physical two-Ptw-projector coherent sum of original
FULL D20 signed Delta weights restricted to an arbitrary sparse
complementary-divisor fibre S is equal to the complete UNMODIFIED
D20 cell-centering mixed difference of the ZERO-EXTENDED physical
kernel with both projectors still inside.

No belief about smoothness of the sharp source masks, no replacement
of the original D20 full-cell ratio by a ratio on S, and no spurious
cancellation on the short complementary-divisor fibre. Every source
complex K, Mellin/character phase, original graph and Fock OLD mask
may be encoded unchanged into H, eSrc and eTgt. -/
theorem source_original_D20_true_projected_sparse_mixed434
    (Δ W y : ℝ) (hΔ : 0 < Δ) (hWy : W ≤ y)
    (j₁ j₂ : ℕ) (S : Finset (ℕ × ℕ))
    (hS : S ⊆ (sourceD20LogCell Δ j₁).product
      (sourceD20LogCell Δ j₂))
    (H : ℕ → ℕ → ℂ) (eSrc eTgt : ℕ × ℕ → ℂ)
    (M : ℕ) (m₀ t₀ : ℕ) :
    let P : ℕ × ℕ → ℂ := fun i =>
      originalD61ParityProjector434 M (eSrc i) *
      originalD61ParityProjector434 M (eTgt i)
    let K : ℕ → ℕ → ℂ := fun m t =>
      if (m,t)∈S then H m t*P (m,t) else 0
    (∑ i ∈ S,
      sourceD20FullPairCoefficient434 Δ W y H i * P i) =
    ∑ m ∈ sourceD20LogCell Δ j₁,
      ∑ t ∈ sourceD20LogCell Δ j₂,
        ((sourceD20FullDelta Δ W y m:ℝ):ℂ)*
        ((sourceD20FullDelta Δ W y t:ℝ):ℂ)*
          (K m t-K m t₀-K m₀ t+K m₀ t₀) := by
  classical
  let P : ℕ × ℕ → ℂ := fun i =>
    originalD61ParityProjector434 M (eSrc i) *
    originalD61ParityProjector434 M (eTgt i)
  let K : ℕ → ℕ → ℂ := fun m t =>
    if (m,t)∈S then H m t*P (m,t) else 0
  have hMixed := source_original_D20_sparse_mask_full_cell_mixed434
    Δ W y hΔ hWy j₁ j₂ S hS
    (fun i => H i.1 i.2 * P i) m₀ t₀
  change (∑ i ∈ S,
    sourceD20FullPairCoefficient434 Δ W y H i*P i) =
    ∑ m ∈ sourceD20LogCell Δ j₁,
      ∑ t ∈ sourceD20LogCell Δ j₂,
        ((sourceD20FullDelta Δ W y m:ℝ):ℂ)*
        ((sourceD20FullDelta Δ W y t:ℝ):ℂ)*
          (K m t-K m t₀-K m₀ t+K m₀ t₀)
  calc
    _ = ∑ i ∈ S,
      ((sourceD20FullDelta Δ W y i.1:ℝ):ℂ)*
      ((sourceD20FullDelta Δ W y i.2:ℝ):ℂ)*
        (H i.1 i.2*P i) := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [sourceD20FullPairCoefficient434]
      ring
    _ = _ := by simpa only [K] using hMixed
end Green64ComparisonPartial

end

end

/-! ## D20WeightedMixedL2Space -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64ComparisonPartial
open Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- True ORIGINAL FULL D20 centering on complete log cells, with
sharp sparse complementary-divisor fibre S and BOTH physical parity
projectors. The coherent amplitude is bounded by WEIGHTED L2 of
the exact zero-extended masked mixed second difference, with no
pointwise mixed-variation hypothesis or source-cell cardinality cost.
Weights are original signed Delta masses; the pointwise ratio is
never recomputed on the sparse support. -/
theorem green64_original_D20_sparse_projected_weighted_mixed_L2_434
    (Δ W y : ℝ) (hΔ : 0 < Δ) (hWy : W ≤ y)
    (j₁ j₂ : ℕ) (S : Finset (ℕ × ℕ))
    (hS : S ⊆ (sourceD20LogCell Δ j₁).product
      (sourceD20LogCell Δ j₂))
    (H : ℕ → ℕ → ℂ) (eSrc eTgt : ℕ × ℕ → ℂ)
    (M : ℕ) (m₀ t₀ : ℕ) :
    let P : ℕ × ℕ → ℂ := fun i =>
      originalD61ParityProjector434 M (eSrc i) *
      originalD61ParityProjector434 M (eTgt i);
    let K : ℕ → ℕ → ℂ := fun m t =>
      if (m,t)∈S then H m t*P (m,t) else 0;
    let I := (sourceD20LogCell Δ j₁).product
      (sourceD20LogCell Δ j₂);
    let d : ℕ × ℕ → ℝ := fun i =>
      sourceD20FullDelta Δ W y i.1 * sourceD20FullDelta Δ W y i.2;
    let F : ℕ × ℕ → ℂ := fun i =>
      K i.1 i.2-K i.1 t₀-K m₀ i.2+K m₀ t₀;
    ‖∑ i ∈ S, sourceD20FullPairCoefficient434 Δ W y H i * P i‖^2 ≤
      (∑ i ∈ I, |d i|) *
      (∑ i ∈ I, |d i| * ‖F i‖^2) := by
  classical
  let P : ℕ × ℕ → ℂ := fun i =>
    originalD61ParityProjector434 M (eSrc i) *
    originalD61ParityProjector434 M (eTgt i)
  let K : ℕ → ℕ → ℂ := fun m t =>
    if (m,t)∈S then H m t*P (m,t) else 0
  let I := (sourceD20LogCell Δ j₁).product (sourceD20LogCell Δ j₂)
  let d : ℕ × ℕ → ℝ := fun i =>
    sourceD20FullDelta Δ W y i.1 * sourceD20FullDelta Δ W y i.2
  let F : ℕ × ℕ → ℂ := fun i =>
    K i.1 i.2-K i.1 t₀-K m₀ i.2+K m₀ t₀
  have hCenter := source_original_D20_true_projected_sparse_mixed434
    Δ W y hΔ hWy j₁ j₂ S hS H eSrc eTgt M m₀ t₀
  have hProduct :
      (∑ m ∈ sourceD20LogCell Δ j₁,
        ∑ t ∈ sourceD20LogCell Δ j₂,
          ((sourceD20FullDelta Δ W y m:ℝ):ℂ)*
          ((sourceD20FullDelta Δ W y t:ℝ):ℂ)*
            (K m t-K m t₀-K m₀ t+K m₀ t₀)) =
      ∑ i ∈ I, ((d i:ℝ):ℂ)*F i := by
    dsimp only [I]
    change (∑ m ∈ sourceD20LogCell Δ j₁,
       ∑ t ∈ sourceD20LogCell Δ j₂, _) =
       (∑ i ∈ ((sourceD20LogCell Δ j₁) ×ˢ
        (sourceD20LogCell Δ j₂)), ((d i:ℝ):ℂ)*F i)
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only [F,d]
    push_cast
    ring
  have hEq :
      (∑ i ∈ S,sourceD20FullPairCoefficient434 Δ W y H i * P i) =
      ∑ i ∈ I, ((d i:ℝ):ℂ)*F i :=
    hCenter.trans hProduct
  change ‖∑ i ∈ S,sourceD20FullPairCoefficient434 Δ W y H i * P i‖^2 ≤
      (∑ i ∈ I, |d i|) * (∑ i ∈ I, |d i| * ‖F i‖^2)
  rw [hEq]
  exact green64_finite_signed_complex_L2_Cauchy434 I d F
end Green64ComparisonPartial

end

end

/-! ## D20VarianceWeightedMixed -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64ComparisonPartial
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Quantitative ORIGINAL source full-cell D20 weighted mixed L2:
the coherent squared sparse amplitude pays 4 times the actual
complete-cell variances V1*V2 (not the number of divisors or cells),
times the TRUE mixed second difference of the zero-extended
parity-projected sharp sparse kernel. Neither variance is recentered
on the sparse complementary-divisor support. -/
theorem green64_original_D20_sparse_projected_variance_mixed_L2_434
    (Δ W y : ℝ) (hΔ : 0 < Δ) (hWy : W ≤ y)
    (j₁ j₂ : ℕ) (S : Finset (ℕ × ℕ))
    (hS : S ⊆ (sourceD20LogCell Δ j₁).product
      (sourceD20LogCell Δ j₂))
    (H : ℕ → ℕ → ℂ) (eSrc eTgt : ℕ × ℕ → ℂ)
    (M : ℕ) (m₀ t₀ : ℕ) :
    let C1 := sourceD20LogCell Δ j₁;
    let C2 := sourceD20LogCell Δ j₂;
    let A1 : ℝ := ((C1.filter (sourceD20Rough y)).card:ℝ);
    let B1 : ℝ := ((C1.filter (sourceD20Rough W)).card:ℝ);
    let A2 : ℝ := ((C2.filter (sourceD20Rough y)).card:ℝ);
    let B2 : ℝ := ((C2.filter (sourceD20Rough W)).card:ℝ);
    let P : ℕ × ℕ → ℂ := fun i =>
      originalD61ParityProjector434 M (eSrc i)*
      originalD61ParityProjector434 M (eTgt i);
    let K : ℕ → ℕ → ℂ := fun m t =>
      if (m,t)∈S then H m t*P (m,t) else 0;
    let I := C1.product C2;
    let d : ℕ × ℕ → ℝ := fun i =>
      sourceD20FullDelta Δ W y i.1 * sourceD20FullDelta Δ W y i.2;
    let F : ℕ × ℕ → ℂ := fun i =>
      K i.1 i.2-K i.1 t₀-K m₀ i.2+K m₀ t₀;
    ‖∑ i ∈ S, sourceD20FullPairCoefficient434 Δ W y H i*P i‖^2 ≤
      4*(A1*(B1-A1)/B1)*(A2*(B2-A2)/B2) *
      (∑ i ∈ I, |d i| * ‖F i‖^2) := by
  classical
  let C1 := sourceD20LogCell Δ j₁
  let C2 := sourceD20LogCell Δ j₂
  let A1 : ℝ := ((C1.filter (sourceD20Rough y)).card:ℝ)
  let B1 : ℝ := ((C1.filter (sourceD20Rough W)).card:ℝ)
  let A2 : ℝ := ((C2.filter (sourceD20Rough y)).card:ℝ)
  let B2 : ℝ := ((C2.filter (sourceD20Rough W)).card:ℝ)
  let P : ℕ × ℕ → ℂ := fun i =>
    originalD61ParityProjector434 M (eSrc i)*
    originalD61ParityProjector434 M (eTgt i)
  let K : ℕ → ℕ → ℂ := fun m t =>
    if (m,t)∈S then H m t*P (m,t) else 0
  let I := C1.product C2
  let d : ℕ × ℕ → ℝ := fun i =>
    sourceD20FullDelta Δ W y i.1 * sourceD20FullDelta Δ W y i.2
  let F : ℕ × ℕ → ℂ := fun i =>
    K i.1 i.2-K i.1 t₀-K m₀ i.2+K m₀ t₀
  have hEnergy := green64_original_D20_sparse_projected_weighted_mixed_L2_434
    Δ W y hΔ hWy j₁ j₂ S hS H eSrc eTgt M m₀ t₀
  have hMass := green64_original_D20_full_pair_L1_exact434
    Δ W y hΔ hWy j₁ j₂
  change ‖∑ i ∈ S,sourceD20FullPairCoefficient434 Δ W y H i*P i‖^2 ≤
    (∑ i ∈ I, |d i|)*(∑ i ∈ I, |d i| *‖F i‖^2) at hEnergy
  change (∑ i ∈ I, |d i|) =
    4*(A1*(B1-A1)/B1)*(A2*(B2-A2)/B2) at hMass
  change ‖∑ i ∈ S,sourceD20FullPairCoefficient434 Δ W y H i*P i‖^2 ≤
    4*(A1*(B1-A1)/B1)*(A2*(B2-A2)/B2) *
      (∑ i ∈ I, |d i| *‖F i‖^2)
  rw [← hMass]
  exact hEnergy
end Green64ComparisonPartial

end

end

/-! ## SourceOriginalComparisonArc -/

section

open MeasureTheory Filter
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option maxHeartbeats 15000000

/-- Source discrepancy, not an assumed energy, gives BOTH signed first-endpoint
arc estimates at any real decay order. Denominator and product-modulus
conditions are derived from the fixed exponent and the actual rough scale. -/
theorem eventually_source_data_signed_arc434 (cfg : SourceComparisonFixed434) (target : ℝ) :
    ∃ Karc : ℝ, 0 < Karc ∧ ∃ B : ℕ, ∃ X0 : ℝ, 3 ≤ X0 ∧
      ∀ᶠ L : ℝ in atTop, ∀ x : ℝ, X0 ≤ x → L = Real.log x → 3 ≤ L →
      ∀ Y Hprime : ℝ, ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β],
      ∀ d : SourceComparisonData434 ι β cfg x L Y Hprime,
      SourceAlphaDiscrepancy L (B:ℝ) x d.alpha →
      ∀ (eps : Bool) (den h : ℕ), 0 < den → (den:ℝ) ≤ L^cfg.cm →
      (∫ beta in {beta : ℝ | |beta| ≤ L^cfg.Carc/Hprime},
        ‖sourceCircleFourierPoly d.support
          (sourceSignedCoefficients434 d.Ptw eps d.endpoint)
          (((h:ℝ)/(den:ℝ)+beta:ℝ):AddCircle (1:ℝ))‖^2) ≤
        Karc*Y*L^(-target) := by
  obtain ⟨Karc,hKarc,B,X0,hX0,hRaw⟩ := eventually_source_original_arc_conclusion434
    cfg.aexp cfg.bexp cfg.cexp cfg.Carc cfg.CZ cfg.τ cfg.η cfg.Cχ cfg.C0 cfg.q0 cfg.vmin
    cfg.tmax cfg.ea cfg.ec cfg.s0 cfg.cm (Nat.ceil target) cfg.s1base cfg.vexp cfg.fcut cfg.epsi
    cfg.A cfg.Cpsi cfg.Kpsi cfg.hA cfg.hCpsi cfg.hKpsi cfg.hepsi cfg.hFcut
    cfg.haexp cfg.hab cfg.hb cfg.hbc cfg.hτ cfg.hτη cfg.hη cfg.hCχ cfg.hC0
    cfg.hCarc cfg.hq0 cfg.hq1 cfg.hv
  refine ⟨Karc,hKarc,B,X0,hX0,?_⟩
  filter_upwards [hRaw] with L hRawL
  intro x hx hLog hL Y Hprime ι β _ _ _ _ d hDisc eps den h hden hDenCap
  have hLone : 1 ≤ L := by linarith
  have hDenChar : (den:ℝ) ≤ L^cfg.Cχ := hDenCap.trans (by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hLone cfg.hcmChar)
  have hDenOriginal : (den:ℝ) ≤ L^cfg.Carc := hDenCap.trans (by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hLone cfg.hcmArc)
  have hModW : ((d.qBase*den:ℕ):ℝ) ≤ Real.exp (Real.sqrt L) := by
    calc
      _ = (d.qBase:ℝ)*(den:ℝ) := by push_cast; rfl
      _ ≤ L^cfg.cm*L^cfg.cm := mul_le_mul d.hBaseCap hDenCap (by positivity) (by positivity)
      _ = L^(2*cfg.cm) := by rw [←pow_add]; congr 1; omega
      _ ≤ _ := d.hModScale
  have hSource := hRawL x hx hLog hL Y Hprime d.Z d.hY d.hYmax d.hH
    d.hYstrong d.hZ d.hYIdent d.hSmallGroups d.hBigGroups
    d.lo d.hi d.Ncap d.alpha d.hNcap d.hCap d.hAlpha hDisc
    d.G (if eps then d.Ptw else ∅) d.S d.primeSlot d.Ts d.Tb
    d.Vs d.Vsmall d.Vbig d.ts d.tb d.coef d.k d.qBase den h d.c d.chi0
    d.hBase hden d.hBaseCap hDenCap hDenChar d.hk d.hVs d.hts d.htb
    d.hVsmall d.hVbig d.hcoef d.C d.hC d.hCBudget d.hcBound
    d.sigma0 d.sigma1 d.hSigma0 d.hSigma1 (Real.exp (Real.sqrt L)) hModW
    d.hSG d.hSPrime d.hSN d.hPN d.hRough d.hGroup d.hLong d.I d.hI d.hSmall d.hSlot d.hIBand
    d.F1 d.F2 d.p1 d.p2 d.U1 d.U2 d.hF1 d.hF2 d.hp1 d.hp2 d.hmin1 d.hmin2
    d.hU1 d.hU2 d.hcell1 d.hcell2 d.hHIdent d.psi1 d.hSmooth d.hSupport
    d.v1 d.hv1 d.hBudget d.hG (source_parity_choice_subset434 _ _ d.hParity eps)
    d.hTsPrime d.hTbPrime d.hRough hDenOriginal d.hOrigW d.hOrigSmall d.hOrigLong
    d.hSlotMin d.hHband d.hArcCap d.hDisjS d.hDisjB
  have hArc := (source_original_full_signed_arc_iff434
    d.Ncap d.qBase d.S d.Ts d.Tb cfg.q0 d.Vs d.Vsmall d.Vbig d.ts d.tb d.coef d.k
    d.primeSlot d.Ptw d.alphaCut d.c d.chi0 d.sigma0 d.sigma1 d.cutoff
    eps L Y Hprime cfg.Carc (Nat.ceil target:ℝ) Karc h den).mp hSource
  change (∫ beta in {beta : ℝ | |beta| ≤ L^cfg.Carc/Hprime},
    ‖sourceCircleFourierPoly d.support (sourceSignedCoefficients434 d.Ptw eps d.endpoint)
      (((h:ℝ)/(den:ℝ)+beta:ℝ):AddCircle (1:ℝ))‖^2) ≤ _ at hArc
  have hY0 : 0 ≤ Y := by linarith [d.hY]
  exact hArc.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hLone (neg_le_neg (Nat.le_ceil target)))
    (mul_nonneg hKarc.le hY0))
end Green64Analytic.CorrelationSquare

end

