module

public import Green64.Library.Correlation.Part037
public import Green64.Library.Correlation.Part038
public import Green64.Library.Weights.Part018

@[expose] public section

/-!
# Weights / ActualGlobalKernelL2

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualGlobalKernelL2 -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/- Sharp finite duality is used only as the bridge from the existing
actual character synthesis frame to the original physical kernel.
No rowwise smallness or small Gram premise is assumed in the final theorem. -/
private theorem frame_analysis_synthesis_energy
    {X A : Type} [Fintype X] [Fintype A]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (v : X → A → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hSynth : ∀ a : A → ℂ,
      (∑ x : X, w x*‖∑ c : A, v x c*a c‖^2) ≤
        R*(∑ c : A, ‖a c‖^2))
    (f : X → ℂ) :
    (∑ x : X, w x*‖∑ c : A, v x c*
      (∑ y : X, (w y:ℂ)*star (v y c)*f y)‖^2) ≤
      R^2*(∑ x : X, w x*‖f x‖^2) := by
  classical
  let a : A → ℂ := fun c => ∑ y : X, (w y:ℂ)*star (v y c)*f y
  let s : X → ℂ := fun x => ∑ c : A, v x c*a c
  let E : ℝ := ∑ c : A, ‖a c‖^2
  let F : ℝ := ∑ x : X, w x*‖f x‖^2
  let H : ℝ := ∑ x : X, w x*‖s x‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hF : 0 ≤ F := Finset.sum_nonneg
    (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
  have hPair :
      (∑ x : X, (w x:ℂ)*(star (s x)*f x)) = (E:ℂ) := by
    calc
      _ = ∑ x : X, ∑ c : A,
          (w x:ℂ)*(star (a c)*star (v x c)*f x) := by
        simp only [s, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
      _ = ∑ c : A, ∑ x : X,
          (w x:ℂ)*(star (a c)*star (v x c)*f x) := Finset.sum_comm
      _ = ∑ c : A, star (a c)*a c := by
        apply Finset.sum_congr rfl
        intro c hc
        change _ = star (a c)*(∑ x : X, (w x:ℂ)*star (v x c)*f x)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = (E:ℂ) := by
        dsimp only [E]
        rw [Complex.ofReal_sum]
        apply Finset.sum_congr rfl
        intro c hc
        simpa only [Complex.star_def, Complex.normSq_eq_norm_sq] using
          (Complex.normSq_eq_conj_mul_self (z := a c)).symm
  have hCS := source_original_finite_weighted_complex_kernel_CS434
    w hw (fun x => star (s x)) f
  rw [hPair] at hCS
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hE, norm_star] at hCS
  have hHS : H ≤ R*E := hSynth a
  have hEE : E*E ≤ E*(R*F) := by
    have hb := mul_le_mul_of_nonneg_right hHS hF
    change E^2 ≤ H*F at hCS
    nlinarith
  have hEF : E ≤ R*F := by
    by_cases hzero : E=0
    · rw [hzero]
      exact mul_nonneg hR hF
    · have hpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hzero)
      by_contra hh
      have hp := mul_pos hpos (sub_pos.mpr (lt_of_not_ge hh))
      nlinarith
  change H ≤ R^2*F
  calc
    H ≤ R*E := hHS
    _ ≤ R*(R*F) := mul_le_mul_of_nonneg_left hEF hR
    _ = R^2*F := by ring


private theorem conditioned_frame_energy
    {X A : Type} [Fintype X] [Fintype A]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (chi : X → A → ℂ) (gate : X → Prop)
    (nu R : ℝ) (hnu : 0 < nu) (hR : 0 ≤ R)
    (hGram : ∀ a : A → ℂ,
      (∑ c : A, ‖∑ d : A,
        (∑ x : X,
          ((if gate x then w x/nu else 0):ℝ) *
            star (chi x c)*chi x d)*a d‖^2) ≤
        R^2*(∑ c : A, ‖a c‖^2))
    (f : X → ℂ) :
    (∑ p : X, w p *
      ‖(if gate p then (nu:ℂ)⁻¹ *
        ∑ c : A, star (chi p c) *
          ∑ q : X, (w q:ℂ)*(if gate q then chi q c*f q else 0)
        else 0)‖^2) ≤
      R^2*(∑ p : X, if gate p then w p*‖f p‖^2 else 0) := by
  classical
  let W : X → ℝ := fun x => if gate x then w x/nu else 0
  have hW (x : X) : 0 ≤ W x := by
    dsimp [W]
    split_ifs
    · exact div_nonneg (hw x) hnu.le
    · exact le_rfl
  have hSynth (a : A → ℂ) :
      (∑ x : X, W x*‖∑ c : A, star (chi x c)*a c‖^2) ≤
        R*(∑ c : A, ‖a c‖^2) := by
    have hh := source_original_finite_gram_synthesis_frame434
      W hW chi (fun c => star (a c)) R hR (hGram (fun c => star (a c)))
    have hConj (x : X) :
        (∑ c : A, star (chi x c)*a c) =
          star (∑ c : A, chi x c*star (a c)) := by
      simp only [star_sum,star_mul,star_star]
      apply Finset.sum_congr rfl
      intro c hc
      ring
    simpa only [hConj,norm_star] using hh
  have hEnergy := frame_analysis_synthesis_energy
    W hW (fun x c => star (chi x c)) R hR hSynth f
  simp only [star_star] at hEnergy
  let s : X → ℂ := fun p =>
    ∑ c : A, star (chi p c) *
      ∑ q : X, (W q:ℂ)*chi q c*f q
  have hInner (c : A) :
      (∑ q : X, (W q:ℂ)*chi q c*f q) =
        (nu:ℂ)⁻¹ * ∑ q : X,
          (w q:ℂ)*(if gate q then chi q c*f q else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hgate : gate q
    · simp only [W,if_pos hgate,Complex.ofReal_div,div_eq_mul_inv,
        Complex.ofReal_mul,Complex.ofReal_inv]
      ring
    · simp [W,hgate]
  have hs (p : X) :
      s p = (nu:ℂ)⁻¹ * ∑ c : A, star (chi p c) *
        ∑ q : X, (w q:ℂ)*(if gate q then chi q c*f q else 0) := by
    dsimp only [s]
    simp_rw [hInner]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    ring
  have hOut (p : X) :
      w p * ‖(if gate p then (nu:ℂ)⁻¹ *
        ∑ c : A, star (chi p c) *
          ∑ q : X, (w q:ℂ)*(if gate q then chi q c*f q else 0)
        else 0)‖^2 = nu*(W p*‖s p‖^2) := by
    by_cases hp : gate p
    · simp only [if_pos hp,←hs p,W]
      field_simp
    · simp [hp,W]
  have hIn (p : X) :
      (if gate p then w p*‖f p‖^2 else 0) =
        nu*(W p*‖f p‖^2) := by
    by_cases hp : gate p
    · simp only [if_pos hp,W]
      field_simp
    · simp [hp,W]
  calc
    _ = nu*(∑ p : X, W p*‖s p‖^2) := by
      simp_rw [hOut]
      rw [Finset.mul_sum]
    _ ≤ nu*(R^2*(∑ p : X, W p*‖f p‖^2)) :=
      mul_le_mul_of_nonneg_left hEnergy hnu.le
    _ = R^2*(∑ p : X, if gate p then w p*‖f p‖^2 else 0) := by
      simp_rw [hIn]
      rw [←Finset.mul_sum]
      ring


private theorem actual_cell_energy_from_entries
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmuPos : ∀ k p, p ∈ S k → 0 ≤ mu k p)
    (h : ℝ) (j : ℤ) (Q : ℕ)
    (hBIG : ∀ k p, p ∈ S k → p.Prime ∧ Q^2 < p)
    (xi eps : ℝ) (hxi : 0 < xi) (heps : 0 ≤ eps)
    (hMass : xi ≤ sourceOriginalRealGramCellMass434 S mu h j)
    (hoff : ∀ c d : sourceOriginalPrimitiveFamily434 Q, c ≠ d →
      ‖sourceOriginalActualPrimitiveGramEntry434
        S mu h j Q c.val d.val‖ ≤ eps)
    (f : SourceOriginalGramPrimeTuple434 S → ℂ) :
    (∑ p : SourceOriginalGramPrimeTuple434 S,
      sourceOriginalGramPrimeMass434 S mu p *
      ‖∑ q : SourceOriginalGramPrimeTuple434 S,
        (sourceOriginalGramPrimeMass434 S mu q:ℂ) *
        sourceOriginalActualPrimitiveGlobalKernel434
          Q {j} h (sourceOriginalRealGramCellMass434 S mu h)
          (sourceOriginalGramPrimeProduct434 S p)
          (sourceOriginalGramPrimeProduct434 S q) * f q‖^2) ≤
      (1+(Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ)*
        (eps/xi))^2 *
      (∑ p : SourceOriginalGramPrimeTuple434 S,
        if sourceOriginalLiteralLogCell434 h j
          (sourceOriginalGramPrimeProduct434 S p)
        then sourceOriginalGramPrimeMass434 S mu p*‖f p‖^2 else 0) := by
  classical
  let X := SourceOriginalGramPrimeTuple434 S
  let A := sourceOriginalPrimitiveFamily434 Q
  let w : X → ℝ := sourceOriginalGramPrimeMass434 S mu
  let gate : X → Prop := fun p =>
    sourceOriginalLiteralLogCell434 h j (sourceOriginalGramPrimeProduct434 S p)
  let chi : X → A → ℂ := fun p c =>
    c.val.2 ((sourceOriginalGramPrimeProduct434 S p:ℕ):ZMod (c.val.1.val+1))
  let nu := sourceOriginalRealGramCellMass434 S mu h j
  let W : X → ℝ := fun p => if gate p then w p/nu else 0
  let H : A → A → ℂ := fun c d =>
    ∑ p : X, (W p:ℂ)*star (chi p c)*chi p d
  let R := 1+(Fintype.card A:ℝ)*(eps/xi)
  have hnu : 0 < nu := hxi.trans_le hMass
  have hnuC : (nu:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnu.ne'
  have hw (p : X) : 0 ≤ w p :=
    source_original_gram_full_prime_mass_nonneg434 S mu hmuPos p
  have hR : 0 ≤ R := add_nonneg (by norm_num)
    (mul_nonneg (Nat.cast_nonneg _) (div_nonneg heps hxi.le))
  have hEntry (c d : A) :
      H c d = sourceOriginalActualPrimitiveGramEntry434
        S mu h j Q c.val d.val / (nu:ℂ) := by
    unfold sourceOriginalActualPrimitiveGramEntry434 sourceOriginalGramCellEntry434
    dsimp only [H]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hg : gate p
    · have hg' : sourceOriginalLiteralLogCell434 h j
          (sourceOriginalGramPrimeProduct434 S p) := hg
      simp only [W,if_pos hg,if_pos hg',Complex.ofReal_div,div_eq_mul_inv,
        Complex.ofReal_mul,Complex.ofReal_inv]
      dsimp only [w,chi]
      ring
    · have hg' : ¬sourceOriginalLiteralLogCell434 h j
          (sourceOriginalGramPrimeProduct434 S p) := hg
      simp [W,hg,hg']
  have hDiag (c : A) : ‖H c c‖ ≤ 1 := by
    rw [hEntry,source_original_actual_primitive_gram_diagonal434 S mu h j Q c.val hBIG]
    change ‖(nu:ℂ)/(nu:ℂ)‖ ≤ 1
    simp [hnuC]
  have hOff (c d : A) (hne : c ≠ d) : ‖H c d‖ ≤ eps/xi := by
    rw [hEntry,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hnu]
    calc
      _ ≤ eps/nu := div_le_div_of_nonneg_right (hoff c d hne) hnu.le
      _ ≤ eps/xi := div_le_div_of_nonneg_left heps hxi hMass
  have hGram (a : A → ℂ) :
      (∑ c : A, ‖∑ d : A, H c d*a d‖^2) ≤ R^2*(∑ c : A, ‖a c‖^2) :=
    Green64FullPhysicalE.memory_original_finite_cell_gram_schur
      H (eps/xi) (div_nonneg heps hxi.le) hDiag hOff a
  have hb := conditioned_frame_energy w hw chi gate nu R hnu hR hGram f
  simp_rw [source_original_actual_physical_frame_operator_exact434 S mu h j Q f]
  exact hb


/- Orthogonality uses the actual log-cell geometry, before any
absolute values are taken across cells. -/
private theorem actual_global_energy_from_entries
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmuPos : ∀ k p, p ∈ S k → 0 ≤ mu k p)
    (h : ℝ) (hh : 0 < h) (active : Finset ℤ) (Q : ℕ)
    (hBIG : ∀ k p, p ∈ S k → p.Prime ∧ Q^2 < p)
    (xi eps : ℝ) (hxi : 0 < xi) (heps : 0 ≤ eps)
    (hMass : ∀ j ∈ active, xi ≤ sourceOriginalRealGramCellMass434 S mu h j)
    (hoff : ∀ j ∈ active, ∀ c d : sourceOriginalPrimitiveFamily434 Q, c ≠ d →
      ‖sourceOriginalActualPrimitiveGramEntry434
        S mu h j Q c.val d.val‖ ≤ eps)
    (f : SourceOriginalGramPrimeTuple434 S → ℂ) :
    (∑ p : SourceOriginalGramPrimeTuple434 S,
      sourceOriginalGramPrimeMass434 S mu p *
      ‖∑ q : SourceOriginalGramPrimeTuple434 S,
        (sourceOriginalGramPrimeMass434 S mu q:ℂ) *
        sourceOriginalActualPrimitiveGlobalKernel434
          Q active h (sourceOriginalRealGramCellMass434 S mu h)
          (sourceOriginalGramPrimeProduct434 S p)
          (sourceOriginalGramPrimeProduct434 S q) * f q‖^2) ≤
      (1+(Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ)*
        (eps/xi))^2 *
      (∑ p : SourceOriginalGramPrimeTuple434 S,
        sourceOriginalGramPrimeMass434 S mu p*‖f p‖^2) := by
  classical
  let X := SourceOriginalGramPrimeTuple434 S
  let w : X → ℝ := sourceOriginalGramPrimeMass434 S mu
  let gate : ℤ → X → Prop := fun j p =>
    sourceOriginalLiteralLogCell434 h j (sourceOriginalGramPrimeProduct434 S p)
  let row : ℤ → X → ℂ := fun j p =>
    ∑ q : X, (w q:ℂ) *
      sourceOriginalActualPrimitiveGlobalKernel434
        Q {j} h (sourceOriginalRealGramCellMass434 S mu h)
        (sourceOriginalGramPrimeProduct434 S p)
        (sourceOriginalGramPrimeProduct434 S q) * f q
  let R := 1+(Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ)*(eps/xi)
  have hw (p : X) : 0 ≤ w p :=
    source_original_gram_full_prime_mass_nonneg434 S mu hmuPos p
  have hZero (j : ℤ) (p : X) (hp : ¬gate j p) : row j p = 0 := by
    dsimp only [row,w]
    rw [source_original_actual_physical_frame_operator_exact434 S mu h j Q f p]
    exact if_neg hp
  have hSplit (p : X) :
      (∑ q : X, (w q:ℂ) *
        sourceOriginalActualPrimitiveGlobalKernel434
          Q active h (sourceOriginalRealGramCellMass434 S mu h)
          (sourceOriginalGramPrimeProduct434 S p)
          (sourceOriginalGramPrimeProduct434 S q) * f q) =
        ∑ j ∈ active, row j p := by
    simp only [row,sourceOriginalActualPrimitiveGlobalKernel434,
      sourceOriginalCharacterCellKernel434,Finset.sum_singleton,
      Finset.mul_sum,Finset.sum_mul]
    exact Finset.sum_comm
  have hOrth (p : X) :
      ‖∑ j ∈ active, row j p‖^2 = ∑ j ∈ active, ‖row j p‖^2 := by
    by_cases he : ∃ j ∈ active, gate j p
    · obtain ⟨j,hj,hjp⟩ := he
      have hz (k : ℤ) (_hk : k ∈ active) (hkj : k ≠ j) : row k p = 0 := by
        apply hZero
        intro hkp
        exact hkj (source_original_literal_log_cells_unique434
          h hh _ k j hkp hjp)
      have hs : (∑ k ∈ active, row k p) = row j p :=
        Finset.sum_eq_single_of_mem j hj hz
      have ht : (∑ k ∈ active, ‖row k p‖^2) = ‖row j p‖^2 :=
        Finset.sum_eq_single_of_mem j hj
          (fun k hk hkj => by rw [hz k hk hkj]; simp)
      rw [hs,ht]
    · have hz (j : ℤ) (hj : j ∈ active) : row j p = 0 :=
        hZero j p (fun hp => he ⟨j,hj,hp⟩)
      have hsq : (∑ j ∈ active, ‖row j p‖^2) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [hz j hj]
        norm_num
      rw [Finset.sum_eq_zero hz,hsq]
      norm_num
  have hGateSum (p : X) :
      (∑ j ∈ active, if gate j p then w p*‖f p‖^2 else 0) ≤
        w p*‖f p‖^2 := by
    by_cases he : ∃ j ∈ active, gate j p
    · obtain ⟨j,hj,hjp⟩ := he
      have hz (k : ℤ) (_hk : k ∈ active) (hkj : k ≠ j) :
          (if gate k p then w p*‖f p‖^2 else 0) = 0 := by
        apply if_neg
        intro hkp
        exact hkj (source_original_literal_log_cells_unique434 h hh _ k j hkp hjp)
      rw [Finset.sum_eq_single_of_mem j hj hz,if_pos hjp]
    · have hz (j : ℤ) (hj : j ∈ active) : ¬gate j p :=
        fun hp => he ⟨j,hj,hp⟩
      rw [Finset.sum_eq_zero (fun j hj => if_neg (hz j hj))]
      exact mul_nonneg (hw p) (sq_nonneg _)
  have hLocal (j : ℤ) (hj : j ∈ active) :
      (∑ p : X, w p*‖row j p‖^2) ≤
        R^2*(∑ p : X, if gate j p then w p*‖f p‖^2 else 0) :=
    actual_cell_energy_from_entries S mu hmuPos h j Q hBIG
      xi eps hxi heps (hMass j hj) (hoff j hj) f
  change (∑ p : X, w p*‖∑ q : X, (w q:ℂ)*
    sourceOriginalActualPrimitiveGlobalKernel434 Q active h
      (sourceOriginalRealGramCellMass434 S mu h)
      (sourceOriginalGramPrimeProduct434 S p)
      (sourceOriginalGramPrimeProduct434 S q)*f q‖^2) ≤ R^2*(∑ p : X,w p*‖f p‖^2)
  calc
    _ = ∑ p : X, ∑ j ∈ active, w p*‖row j p‖^2 := by
      simp_rw [hSplit,hOrth,Finset.mul_sum]
    _ = ∑ j ∈ active, ∑ p : X, w p*‖row j p‖^2 := Finset.sum_comm
    _ ≤ ∑ j ∈ active, R^2*(∑ p : X,
        if gate j p then w p*‖f p‖^2 else 0) :=
      Finset.sum_le_sum hLocal
    _ = R^2*(∑ p : X, ∑ j ∈ active,
        if gate j p then w p*‖f p‖^2 else 0) := by
      rw [←Finset.mul_sum,Finset.sum_comm]
    _ ≤ R^2*(∑ p : X,w p*‖f p‖^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun p _ => hGateSum p))
        (sq_nonneg R)


/-- The ACTUAL original retained GLOBAL primitive-character kernel,
on the ORIGINAL harmonic prime-tuple space, has operator norm at most
1+(K/Vmin)*L^(-B). All retained log cells are summed INSIDE the operator.
There is no loss from their number, the number of marked coordinates,
or primitive-character cardinality in the final bound.

The only analytic input is the already proved original SW theorem.
Its requested accuracy is B+Cxi+2*Cq, chosen AFTER the conductor and
retention exponents. No hCross, abstract spectral bound, C6 budget
cycle, or smallness of the signed comparison residual is assumed.
Arbitrary complex tests retain their full prime-label dependence. -/
theorem source_original_actual_GLOBAL_kernel_L2_near_one434
    (Cq : ℕ) (Cxi gamma d B : ℝ)
    (hCxi : 0 ≤ Cxi) (hgamma : 0 < gamma)
    (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
      (hmu : ∀ k, ∑ p ∈ S k, mu k p = 1)
      (hmuPos : ∀ k p, p ∈ S k → 0 ≤ mu k p)
      (h : ℝ) (hh : 0 < h) (active : Finset ℤ) (Q : ℕ)
      (i : ι) (hBIG : ∀ k p, p ∈ S k → p.Prime ∧ Q^2 < p)
      (L : ℝ) (hL : 1 ≤ L)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hQ : (Q:ℝ) ≤ L^Cq)
      (u v : ℕ) (hu : 1 ≤ u) (huv : u ≤ v)
      (hv : (v:ℝ) ≤ Real.exp (L^d))
      (huLarge : Real.exp (L^gamma) ≤ ((u+1:ℕ):ℝ))
      (huBIG : Q^2 ≤ u) (hY : Y ≤ ((u+1:ℕ):ℝ))
      (Vmin V : ℝ) (hVmin : 0 < Vmin) (hV : Vmin ≤ V)
      (hBand : S i = sourceOriginalActualPrimeBand434 u v)
      (hWeight : ∀ p, mu i p = (1/(p:ℝ))/V)
      (xi : ℝ) (hxi : 0 < xi) (hXipoly : xi⁻¹ ≤ L^Cxi)
      (hMass : ∀ j ∈ active,
        xi ≤ sourceOriginalRealGramCellMass434 S mu h j)
      (f : SourceOriginalGramPrimeTuple434 S → ℂ),
      (∑ p : SourceOriginalGramPrimeTuple434 S,
        sourceOriginalGramPrimeMass434 S mu p *
        ‖∑ q : SourceOriginalGramPrimeTuple434 S,
          (sourceOriginalGramPrimeMass434 S mu q:ℂ) *
          sourceOriginalActualPrimitiveGlobalKernel434
            Q active h (sourceOriginalRealGramCellMass434 S mu h)
            (sourceOriginalGramPrimeProduct434 S p)
            (sourceOriginalGramPrimeProduct434 S q) * f q‖^2) ≤
        (1+(K/Vmin)*L^(-B))^2 *
        (∑ p : SourceOriginalGramPrimeTuple434 S,
          sourceOriginalGramPrimeMass434 S mu p*‖f p‖^2) := by
  let Bplus : ℝ := (B+Cxi)+((2*Cq:ℕ):ℝ)
  have hBplus : 0 < Bplus := by
    dsimp only [Bplus]
    have hn : (0:ℝ) ≤ ((2*Cq:ℕ):ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨K,Y,hK,hSW⟩ := source_original_actual_big_gram_power_unconditional434
    Cq gamma d Bplus hgamma hd hBplus
  refine ⟨K,Y,hK,?_⟩
  intro ι instF instD S mu hmu hmuPos h hh active Q i hBIG
    L hL hLdyad hQ u v hu huv hv huLarge huBIG hY
    Vmin V hVmin hV hBand hWeight xi hxi hXipoly hMass f
  classical
  let A := sourceOriginalPrimitiveFamily434 Q
  let eps : ℝ := (K/V)*L^(-Bplus)
  let R : ℝ := 1+(Fintype.card A:ℝ)*(eps/xi)
  let T : ℝ := 1+(K/Vmin)*L^(-B)
  have hLpos : 0 < L := by linarith
  have hVpos : 0 < V := hVmin.trans_le hV
  have heps : 0 ≤ eps := mul_nonneg (div_nonneg hK hVpos.le)
    (Real.rpow_nonneg hLpos.le _)
  have hoff (j : ℤ) (_hj : j ∈ active) (c e : A) (hne : c ≠ e) :
      ‖sourceOriginalActualPrimitiveGramEntry434 S mu h j Q c.val e.val‖ ≤ eps := by
    apply hSW S mu hmu hmuPos h j Q c.val e.val c.property e.property
      (fun hvv => hne (Subtype.ext hvv)) i hBIG
      L hL hLdyad hQ u v hu huv hv huLarge huBIG hY V hVpos hBand hWeight
  have hLoss :
      (Fintype.card A:ℝ)*eps ≤ (K/Vmin)*L^(-(B+Cxi)) :=
    source_original_prime_frame_loss_absorb434
      Q Cq L (B+Cxi) K V Vmin hL hQ hK hVmin hV
  have hPower : L^(-(B+Cxi))*L^Cxi = L^(-B) := by
    rw [←Real.rpow_add hLpos]
    congr 1
    ring
  have hSmall :
      (Fintype.card A:ℝ)*(eps/xi) ≤ (K/Vmin)*L^(-B) := by
    calc
      _ = ((Fintype.card A:ℝ)*eps)*xi⁻¹ := by ring
      _ ≤ ((K/Vmin)*L^(-(B+Cxi)))*xi⁻¹ :=
        mul_le_mul_of_nonneg_right hLoss (inv_nonneg.mpr hxi.le)
      _ ≤ ((K/Vmin)*L^(-(B+Cxi)))*L^Cxi :=
        mul_le_mul_of_nonneg_left hXipoly
          (mul_nonneg (div_nonneg hK hVmin.le) (Real.rpow_nonneg hLpos.le _))
      _ = (K/Vmin)*L^(-B) := by rw [mul_assoc,hPower]
  have hR : 0 ≤ R := add_nonneg (by norm_num)
    (mul_nonneg (Nat.cast_nonneg _) (div_nonneg heps hxi.le))
  have hRT : R ≤ T := by dsimp only [R,T]; linarith
  have hE : 0 ≤ ∑ p : SourceOriginalGramPrimeTuple434 S,
      sourceOriginalGramPrimeMass434 S mu p*‖f p‖^2 :=
    Finset.sum_nonneg (fun p _ => mul_nonneg
      (source_original_gram_full_prime_mass_nonneg434 S mu hmuPos p) (sq_nonneg _))
  exact (actual_global_energy_from_entries S mu hmuPos h hh active Q
    hBIG xi eps hxi heps hMass hoff f).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR hRT 2) hE)

/-- A uniform eventual norm bound TWO for the same actual GLOBAL kernel.
The threshold is independent of the number of free prime marks, cells,
Q<=L^Cq, all physical input tests, and every retained mass >=xi with
xi^(-1)<=L^Cxi. No fixed total-probe cap M occurs. This controls the
comparison kernel, not the signed oscillatory comparison residual. -/
theorem eventually_source_original_actual_GLOBAL_kernel_L2_bound_two434
    (Cq : ℕ) (Cxi gamma d : ℝ)
    (hCxi : 0 ≤ Cxi) (hgamma : 0 < gamma)
    (hd : 0 ≤ d) (Vmin : ℝ) (hVmin : 0 < Vmin) :
    ∃ Y : ℝ, ∀ᶠ L : ℝ in atTop,
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
      (hmu : ∀ k, ∑ p ∈ S k, mu k p = 1)
      (hmuPos : ∀ k p, p ∈ S k → 0 ≤ mu k p)
      (h : ℝ) (hh : 0 < h) (active : Finset ℤ) (Q : ℕ)
      (i : ι) (hBIG : ∀ k p, p ∈ S k → p.Prime ∧ Q^2 < p)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hQ : (Q:ℝ) ≤ L^Cq)
      (u v : ℕ) (hu : 1 ≤ u) (huv : u ≤ v)
      (hv : (v:ℝ) ≤ Real.exp (L^d))
      (huLarge : Real.exp (L^gamma) ≤ ((u+1:ℕ):ℝ))
      (huBIG : Q^2 ≤ u) (hY : Y ≤ ((u+1:ℕ):ℝ))
      (V : ℝ) (hV : Vmin ≤ V)
      (hBand : S i = sourceOriginalActualPrimeBand434 u v)
      (hWeight : ∀ p, mu i p = (1/(p:ℝ))/V)
      (xi : ℝ) (hxi : 0 < xi) (hXipoly : xi⁻¹ ≤ L^Cxi)
      (hMass : ∀ j ∈ active,
        xi ≤ sourceOriginalRealGramCellMass434 S mu h j)
      (f : SourceOriginalGramPrimeTuple434 S → ℂ),
      (∑ p : SourceOriginalGramPrimeTuple434 S,
        sourceOriginalGramPrimeMass434 S mu p *
        ‖∑ q : SourceOriginalGramPrimeTuple434 S,
          (sourceOriginalGramPrimeMass434 S mu q:ℂ) *
          sourceOriginalActualPrimitiveGlobalKernel434
            Q active h (sourceOriginalRealGramCellMass434 S mu h)
            (sourceOriginalGramPrimeProduct434 S p)
            (sourceOriginalGramPrimeProduct434 S q) * f q‖^2) ≤
        4 *
        (∑ p : SourceOriginalGramPrimeTuple434 S,
          sourceOriginalGramPrimeMass434 S mu p*‖f p‖^2) := by
  obtain ⟨K,Y,hK,hNear⟩ := source_original_actual_GLOBAL_kernel_L2_near_one434
    Cq Cxi gamma d 1 hCxi hgamma hd (by norm_num)
  refine ⟨Y,?_⟩
  filter_upwards [eventually_ge_atTop (max (1:ℝ) (K/Vmin))] with L hL0
  have hL : 1 ≤ L := (le_max_left _ _).trans hL0
  have hScale : K/Vmin ≤ L := (le_max_right _ _).trans hL0
  have hLpos : 0 < L := by linarith
  intro ι instF instD S mu hmu hmuPos h hh active Q i hBIG
    hLdyad hQ u v hu huv hv huLarge huBIG hY
    V hV hBand hWeight xi hxi hXipoly hMass f
  have hDelta : (K/Vmin)*L^(-(1:ℝ)) ≤ 1 := by
    rw [Real.rpow_neg_one]
    simpa only [div_eq_mul_inv] using ((div_le_one hLpos).mpr hScale)
  have hDelta0 : 0 ≤ (K/Vmin)*L^(-(1:ℝ)) :=
    mul_nonneg (div_nonneg hK hVmin.le) (Real.rpow_nonneg hLpos.le _)
  have hFactor : (1+(K/Vmin)*L^(-(1:ℝ)))^2 ≤ 4 := by nlinarith
  have hEnergy : 0 ≤ ∑ p : SourceOriginalGramPrimeTuple434 S,
      sourceOriginalGramPrimeMass434 S mu p*‖f p‖^2 :=
    Finset.sum_nonneg (fun p _ => mul_nonneg
      (source_original_gram_full_prime_mass_nonneg434 S mu hmuPos p) (sq_nonneg _))
  exact (hNear S mu hmu hmuPos h hh active Q i hBIG
    L hL hLdyad hQ u v hu huv hv huLarge huBIG hY
    Vmin V hVmin hV hBand hWeight xi hxi hXipoly hMass f).trans
      (mul_le_mul_of_nonneg_right hFactor hEnergy)
end Green64Analytic.CorrelationSquare

end

