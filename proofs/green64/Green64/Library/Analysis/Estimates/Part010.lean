module

public import Green64.Library.Sieve.Foundations.Part004
public import Green64.Library.Weights.Part043
public import Green64.Library.Weights.Part016
public import Green64.Library.Weights.Part015
public import Mathlib
public import Green64.Library.Weights.Part017
public import Green64.Library.Weights.Part014
public import Green64.Library.Weights.Part042
public import Green64.Library.Weights.Part018
public import Green64.Library.Weights.Part045

@[expose] public section

/-!
# Analysis / Estimates / Part010

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalRationalUnitFourierCost -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- The explicit complex Dirichlet Fourier coefficient on the
genuine finite unit group has norm at most one whenever the
original residue-class function has norm at most one. This is
a direct average bound, not an assumed Fourier l1 estimate. -/
theorem source_original_rational_unit_fourier_coeff_norm_le_one434
    (q : ℕ) [NeZero q] (F : (ZMod q)ˣ → ℂ)
    (hF : ∀ a, ‖F a‖ ≤ 1)
    (χ : DirichletCharacter ℂ q) :
    ‖sourceOriginalRationalUnitFourierCoeff434 q F χ‖ ≤ 1 := by
  classical
  have hTpos : (0:ℝ) < (q.totient:ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q))
  have hNorm (a : (ZMod q)ˣ) :
      ‖F a * χ ((a:ZMod q)⁻¹)‖ ≤ 1 := by
    rw [norm_mul]
    have hc : ‖χ ((a:ZMod q)⁻¹)‖ ≤ 1 :=
      χ.norm_le_one _
    exact (mul_le_mul (hF a) hc
      (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul 1)
  have hSum :
      ‖∑ a : (ZMod q)ˣ, F a*χ ((a:ZMod q)⁻¹)‖ ≤
        (q.totient:ℝ) := by
    calc
      _ ≤ ∑ a : (ZMod q)ˣ, ‖F a*χ ((a:ZMod q)⁻¹)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _a : (ZMod q)ˣ, (1:ℝ) :=
        Finset.sum_le_sum (fun a ha => hNorm a)
      _ = (Fintype.card (ZMod q)ˣ:ℝ) := by simp
      _ = (q.totient:ℝ) := by
        exact_mod_cast ZMod.card_units_eq_totient q
  unfold sourceOriginalRationalUnitFourierCoeff434
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q.totient:ℝ)⁻¹ * (q.totient:ℝ) :=
      mul_le_mul_of_nonneg_left hSum (inv_nonneg.mpr hTpos.le)
    _ = 1 := by field_simp [hTpos.ne']

/-- Fourier inversion from C104 has polynomially bounded
coefficient mass: an arbitrary unit-norm reduced-residue phase
has sum |cχ| at most φ(q) ≤ q. This loses a √q over the
optimal Parseval bound but is sufficient for arbitrary fixed
log-power precision because SW is uniform with arbitrary
exponent; no L2→L1 conjectural assumption is used. -/
theorem source_original_rational_unit_fourier_l1_le_modulus434
    (q : ℕ) [NeZero q] (F : (ZMod q)ˣ → ℂ)
    (hF : ∀ a, ‖F a‖ ≤ 1) :
    (∑ χ : DirichletCharacter ℂ q,
      ‖sourceOriginalRationalUnitFourierCoeff434 q F χ‖) ≤ (q:ℝ) := by
  classical
  calc
    _ ≤ ∑ _χ : DirichletCharacter ℂ q, (1:ℝ) :=
      Finset.sum_le_sum (fun χ hχ =>
        source_original_rational_unit_fourier_coeff_norm_le_one434
          q F hF χ)
    _ = (Fintype.card (DirichletCharacter ℂ q):ℝ) := by simp
    _ = (q.totient:ℝ) := by
      have hCard : Fintype.card (DirichletCharacter ℂ q) =
          q.totient := by
        simpa only [Nat.card_eq_fintype_card] using
          (DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity
             ℂ q)
      exact_mod_cast hCard
    _ ≤ (q:ℝ) := by
      exact_mod_cast Nat.totient_le q
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTruePrimitiveCharacterNonempty -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- For any genuine positive original conductor cutoff Q,
the TRUE primitive-character family is nonempty: it contains
the primitive trivial character at level 1. This removes an
artificial existential character witness when active original
GLOBAL cells exist, and does not invent a nonprimitive mode. -/
theorem source_original_true_primitive_family_nonempty434
    (Q : ℕ) (hQ : 0 < Q) :
    (sourceOriginalActualPrimitiveCharacters434 Q).Nonempty := by
  classical
  let q : Fin Q := ⟨0,hQ⟩
  let χ : DirichletCharacter ℂ (q.val+1) := 1
  let c : Σ q : Fin Q,DirichletCharacter ℂ (q.val+1) :=
    ⟨q,χ⟩
  refine ⟨c,(source_original_actual_primitive_mem434 Q c).mpr ?_⟩
  change (1 : DirichletCharacter ℂ 1).IsPrimitive
  exact DirichletCharacter.isPrimitive_one_level_one
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualCellProbability -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- The LITERAL source03 cell probability ν_j is the probability,
under the ORIGINAL full independent labelled prime-slot law, that
the complete free product D lies in the half-open logarithmic
cell I_j=[jh,(j+1)h). Repeated numerical primes in different slots
are allowed. -/
noncomputable def sourceOriginalActualCellProbability434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (j : ℤ) : ℝ :=
  ∑ a ∈ Fintype.piFinset S,
    if sourceOriginalLiteralLogCell434 h j (∏ i : ι,a i)
    then sourceSharedLaw434 mu a else 0

/-- For arbitrary nonnegative weights on a finite original source
probability space, half-open logarithmic cells form disjoint
events and their combined probability cannot exceed the total
probability mass. -/
theorem source_original_disjoint_log_cell_mass_bound434
    {State : Type} (states : Finset State)
    (mass : State → ℝ) (prod : State → ℕ)
    (h : ℝ) (hh : 0 < h)
    (active : Finset ℤ)
    (hm : ∀ a ∈ states,0 ≤ mass a) :
    (∑ j ∈ active,∑ a ∈ states,
      if sourceOriginalLiteralLogCell434 h j (prod a)
      then mass a else 0) ≤
    ∑ a ∈ states,mass a := by
  classical
  let gate : ℤ → State → Prop :=
    fun j a => sourceOriginalLiteralLogCell434 h j (prod a)
  have hOne (a : State) (ha : a ∈ states) :
      (∑ j ∈ active,if gate j a then mass a else 0) ≤ mass a := by
    by_cases he : ∃ j ∈ active,gate j a
    · obtain ⟨j,hj,hg⟩ := he
      have hset : active.filter (fun k => gate k a) = {j} := by
        ext k
        simp only [Finset.mem_filter,Finset.mem_singleton]
        constructor
        · rintro ⟨hk,hkg⟩
          exact source_original_literal_log_cells_unique434
            h hh (prod a) k j hkg hg
        · intro heq
          subst k
          exact ⟨hj,hg⟩
      have hEq : (∑ k ∈ active,if gate k a then mass a else 0) =
          mass a := by
        rw [←Finset.sum_filter,hset,Finset.sum_singleton]
      rw [hEq]
    · have hzero : ∀ j ∈ active,¬gate j a := by
        intro j hj hga
        exact he ⟨j,hj,hga⟩
      have hh0 : (∑ j ∈ active,if gate j a then mass a else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        simp only [if_neg (hzero j hj)]
      rw [hh0]
      exact hm a ha
  calc
    _ = ∑ a ∈ states,∑ j ∈ active,
      if gate j a then mass a else 0 := by
      dsimp only [gate]
      rw [Finset.sum_comm]
    _ ≤ ∑ a ∈ states,mass a :=
      Finset.sum_le_sum hOne

/-- The active ν_j are REAL source probabilities under the genuine
unconditional product measure; their total mass is at most one.
This proves the normalization that was previously supplied as an
external assumption in the expanded pattern cost bound. -/
theorem source_original_actual_cell_probability_total434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (hh : 0 < h)
    (active : Finset ℤ)
    (hmu : ∀ i p,p ∈ S i → 0 ≤ mu i p)
    (hMass : ∀ i,∑ p ∈ S i,mu i p = 1) :
    (∑ j ∈ active,sourceOriginalActualCellProbability434 S mu h j) ≤ 1 := by
  classical
  let Ω : Finset (ι → ℕ) := Fintype.piFinset S
  let weight : (ι → ℕ) → ℝ := sourceSharedLaw434 mu
  have hWeight : ∀ a ∈ Ω,0 ≤ weight a :=
    source_shared_law_nonneg434 S mu hmu
  have hFull : (∑ a ∈ Ω,weight a) = 1 :=
    source_shared_law_total434 S mu hMass
  have hh0 := source_original_disjoint_log_cell_mass_bound434 Ω
    weight (fun a => ∏ i : ι,a i) h hh active hWeight
  change (∑ j ∈ active,∑ a ∈ Ω,
    if sourceOriginalLiteralLogCell434 h j (∏ i : ι,a i)
    then weight a else 0) ≤ 1
  exact hh0.trans_eq hFull

/-- At the true prime atom law mu_i(p)=1/(p V_i), the same
active-cell normalization holds without assuming independence of
cell membership from other prime slots. -/
theorem source_original_true_prime_cell_probability_total434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (V : ι → ℝ)
    (h : ℝ) (hh : 0 < h) (active : Finset ℤ)
    (hV : ∀ i,V i=∑ p ∈ S i,1/(p:ℝ))
    (hVp : ∀ i,0 < V i)
    (hPrime : ∀ i p,p ∈ S i → p.Prime) :
    (∑ j ∈ active,
      sourceOriginalActualCellProbability434 S
        (fun i => sourcePrimeSharedAtom434 (V i)) h j) ≤ 1 := by
  apply source_original_actual_cell_probability_total434
    S (fun i => sourcePrimeSharedAtom434 (V i)) h hh active
  · intro i p hp
    have hpPos : (0:ℝ) < p := by exact_mod_cast (hPrime i p hp).pos
    have hVp' := hVp i
    dsimp only [sourcePrimeSharedAtom434]
    positivity
  · intro i
    exact source_prime_shared_atom_total434
      (S i) (V i) (hV i) (hVp i).ne'
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualCellTwoDyads -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- A genuine source03 half-open log cell [jh,(j+1)h), h<=1,
is covered by TWO actual integer dyadic windows anchored at
ceil(exp(jh)). No additional comparison-scale hypothesis.
This fixes both the lower scale and the window's origin. -/
theorem source_original_actual_log_cell_two_integer_dyads434
    (h : ℝ) (hh : h ≤ 1) (j : ℤ)
    (n : ℕ) (hn : 0 < n)
    (hcell : sourceOriginalLiteralLogCell434 h j n) :
    ∃ M : ℕ, 0 < M ∧
      (M = Nat.ceil (Real.exp ((j:ℝ)*h)) ∨
       M = 2*Nat.ceil (Real.exp ((j:ℝ)*h))) ∧
      Real.exp ((j:ℝ)*h) ≤ (M:ℝ) ∧
      M ≤ n ∧ n < 2*M := by
  let U : ℝ := Real.exp ((j:ℝ)*h)
  let M₀ : ℕ := Nat.ceil U
  have hL : Real.log U ≤ Real.log (n:ℝ) := by
    simpa only [U,Real.log_exp] using hcell.1
  have hR : Real.log (n:ℝ) < Real.log U+h := by
    have hh' := hcell.2
    simp only [U,Real.log_exp]
    nlinarith
  have hCover : n ∈ Finset.Ico M₀ (M₀+3*M₀) :=
    source_original_logcell_integer_cover434
      U h (Real.exp_pos _) hh n hn hL hR
  obtain ⟨hM0,hFourRaw⟩ := Finset.mem_Ico.mp hCover
  have hFour : n < 4*M₀ := by omega
  have hMpos : 0 < M₀ := by omega
  have hU : U ≤ (M₀:ℝ) := Nat.le_ceil U
  by_cases ht : n < 2*M₀
  · refine ⟨M₀,hMpos,Or.inl rfl,?_,hM0,ht⟩
    exact hU
  · refine ⟨2*M₀,by omega,Or.inr rfl,?_,?_,?_⟩
    · have hMnonneg : (0:ℝ) ≤ (M₀:ℝ) := Nat.cast_nonneg _
      push_cast
      nlinarith [hU]
    · omega
    · omega
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualCellDyadPartition -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- Every true source03 log-cell supported integer product
lies in the UNION of exactly two deterministic dyads
[M0,2*M0) or [2*M0,4*M0), M0=ceil(exp(jh)).
The cover is independent of the labelled tuple and of
the endpoint test, so it can be inserted inside physical
expectations without a spurious choice of witness. -/
theorem source_original_actual_cell_two_dyad_partition434
    (h : ℝ) (hh : h ≤ 1) (j : ℤ)
    (n : ℕ) (hn : 0 < n)
    (hcell : sourceOriginalLiteralLogCell434 h j n) :
    let M0 : ℕ := Nat.ceil (Real.exp ((j:ℝ)*h))
    0 < M0 ∧
      (n ∈ Finset.Ico M0 (2*M0) ∨
       n ∈ Finset.Ico (2*M0) (4*M0)) := by
  dsimp
  obtain ⟨M,hM,hCase,hUM,hLo,hHi⟩ :=
    source_original_actual_log_cell_two_integer_dyads434
      h hh j n hn hcell
  constructor
  · rcases hCase with ha | hb
    · rw [ha] at hM
      exact hM
    · omega
  · rcases hCase with ha | hb
    · left
      rw [Finset.mem_Ico]
      rw [ha] at hLo hHi
      exact ⟨hLo,hHi⟩
    · right
      rw [Finset.mem_Ico]
      rw [hb] at hLo hHi
      constructor <;> omega
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualPrimitiveKernelExpansion -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11500000

/-- ORIGINAL signed source03 comparison coefficient:
TWO globally primitive character kernels of all conductors q<=Q,
with the true half-open log-cell interval I_j.
The first kernel acts on D_A and TARGET X_A, the second on D_B
and SOURCE X_B, with the original inclusion-exclusion sign. -/
noncomputable def sourceOriginalActualPrimitiveComparisonKernel434
    (Q : ℕ) (JA JB : Finset ℤ) (hA hB : ℝ)
    (massA massB : ℤ → ℝ)
    (DA XA DB XB r : ℕ) : ℂ :=
  -((-1:ℂ)^r)*
    sourceOriginalActualPrimitiveGlobalKernel434
      Q JA hA massA DA XA*
    sourceOriginalActualPrimitiveGlobalKernel434
      Q JB hB massB DB XB

/-- EXACT fourfold source03 expansion, with no change to the
ordered products D_A,X_A(target),D_B,X_B(source), or sign.
The character in each term remembers its primitive conductor. -/
theorem source_original_actual_primitive_comparison_expand434
    (Q : ℕ) (JA JB : Finset ℤ) (hA hB : ℝ)
    (massA massB : ℤ → ℝ)
    (DA XA DB XB r : ℕ) :
    sourceOriginalActualPrimitiveComparisonKernel434
      Q JA JB hA hB massA massB DA XA DB XB r =
    ∑ ja ∈ JA,
      ∑ ca ∈ sourceOriginalActualPrimitiveCharacters434 Q,
        ∑ jb ∈ JB,
          ∑ cb ∈ sourceOriginalActualPrimitiveCharacters434 Q,
            -((-1:ℂ)^r)*
              sourceOriginalCharacterCellAtom434
                (sourceOriginalLiteralLogCell434 hA) massA
                (fun c n => c.2 (n:ZMod (c.1.val+1)))
                ja ca DA XA*
              sourceOriginalCharacterCellAtom434
                (sourceOriginalLiteralLogCell434 hB) massB
                (fun c n => c.2 (n:ZMod (c.1.val+1)))
                jb cb DB XB := by
  classical
  unfold sourceOriginalActualPrimitiveComparisonKernel434
    sourceOriginalActualPrimitiveGlobalKernel434
  exact source_original_comparison_kernel_finite_expand434
    JA (sourceOriginalActualPrimitiveCharacters434 Q)
    JB (sourceOriginalActualPrimitiveCharacters434 Q)
    (sourceOriginalLiteralLogCell434 hA)
    (sourceOriginalLiteralLogCell434 hB)
    massA massB
    (fun c n => c.2 (n:ZMod (c.1.val+1)))
    (fun c n => c.2 (n:ZMod (c.1.val+1)))
    DA XA DB XB r

/-- A finite residual comparison-pattern family is expanded
literally, term-by-term, with the SAME four global indices for
every pattern and with no added pattern multiplicity factor. -/
theorem source_original_actual_primitive_family_expand434
    {Pattern : Type}
    (patterns : Finset Pattern)
    (Q : ℕ) (JA JB : Pattern → Finset ℤ)
    (hA hB : Pattern → ℝ) (massA massB : Pattern → ℤ → ℝ)
    (DA XA DB XB r : Pattern → ℕ) :
    (∑ ν ∈ patterns,
      sourceOriginalActualPrimitiveComparisonKernel434 Q
        (JA ν) (JB ν) (hA ν) (hB ν)
        (massA ν) (massB ν)
        (DA ν) (XA ν) (DB ν) (XB ν) (r ν)) =
    ∑ ν ∈ patterns,
      ∑ ja ∈ JA ν,
        ∑ ca ∈ sourceOriginalActualPrimitiveCharacters434 Q,
          ∑ jb ∈ JB ν,
            ∑ cb ∈ sourceOriginalActualPrimitiveCharacters434 Q,
              -((-1:ℂ)^(r ν))*
                sourceOriginalCharacterCellAtom434
                  (sourceOriginalLiteralLogCell434 (hA ν))
                  (massA ν)
                  (fun c n => c.2 (n:ZMod (c.1.val+1)))
                  ja ca (DA ν) (XA ν)*
                sourceOriginalCharacterCellAtom434
                  (sourceOriginalLiteralLogCell434 (hB ν))
                  (massB ν)
                  (fun c n => c.2 (n:ZMod (c.1.val+1)))
                  jb cb (DB ν) (XB ν) := by
  classical
  apply Finset.sum_congr rfl
  intro ν hν
  exact source_original_actual_primitive_comparison_expand434
    Q (JA ν) (JB ν) (hA ν) (hB ν)
    (massA ν) (massB ν)
    (DA ν) (XA ν) (DB ν) (XB ν) (r ν)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualPhysicalComparisonKnu -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- The literal two-global SOURCE03 primitive-character product
kernel IS the signed coupled K_nu on the physically projected
source/target unshared marks. This discharges any false assumption
that K_nu factors independently by prime group. -/
theorem source_original_actual_primitive_Knu_identification434
    {G : Type} [Fintype G]
    (t : G → ℕ) (Q : ℕ)
    (JA JB : Finset ℤ) (hA hB : ℝ)
    (massA massB : ℤ → ℝ)
    (DA DB r : ℕ)
    (XA XB : (∀ g,Fin (t g) → ℕ) → ℕ)
    (u v : ∀ g,Fin (t g) → ℕ) :
    sourceAuxiliaryOriginalComparisonKnu434 t
      (sourceOriginalActualPrimitiveGlobalKernel434 Q JA hA massA)
      (sourceOriginalActualPrimitiveGlobalKernel434 Q JB hB massB)
      DA DB r XA XB u v =
    sourceOriginalActualPrimitiveComparisonKernel434
      Q JA JB hA hB massA massB
      DA (XA v) DB (XB u) r := by
  rfl

/-- The SOURCE03 comparison coefficient on the TRUE unshared
source/target physical mark products is <= Q^4*xi^-2.
All characters have their genuine original conductor, are
primitive, and no cell-count or character-cardinality premise
is needed: these were proved from true log cells and the
Dirichlet character group. -/
theorem source_original_actual_primitive_physical_Knu_bound434
    {G : Type} [Fintype G]
    (t : G → ℕ) (Q : ℕ) (xi : ℝ)
    (hxi : 0 < xi)
    (JA JB : Finset ℤ) (hA hB : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB)
    (massA massB : ℤ → ℝ)
    (hMassA : ∀ j ∈ JA,xi ≤ massA j)
    (hMassB : ∀ j ∈ JB,xi ≤ massB j)
    (DA DB r : ℕ)
    (XA XB : (∀ g,Fin (t g) → ℕ) → ℕ)
    (u v : ∀ g,Fin (t g) → ℕ) :
    ‖sourceAuxiliaryOriginalComparisonKnu434 t
      (sourceOriginalActualPrimitiveGlobalKernel434 Q JA hA massA)
      (sourceOriginalActualPrimitiveGlobalKernel434 Q JB hB massB)
      DA DB r XA XB u v‖ ≤
      (Q:ℝ)^4*(xi⁻¹)^2 := by
  have hAchar (n : ℕ) :
    ‖sourceOriginalActualPrimitiveGlobalKernel434
      Q JA hA massA DA n‖ ≤ (Q:ℝ)^2*xi⁻¹ :=
    source_original_actual_primitive_global_bound434
      Q JA hA hhA massA xi hxi hMassA DA n
  have hBchar (n : ℕ) :
    ‖sourceOriginalActualPrimitiveGlobalKernel434
      Q JB hB massB DB n‖ ≤ (Q:ℝ)^2*xi⁻¹ :=
    source_original_actual_primitive_global_bound434
      Q JB hB hhB massB xi hxi hMassB DB n
  exact source_auxiliary_original_comparison_Knu_global_bound434
    t
    (sourceOriginalActualPrimitiveGlobalKernel434 Q JA hA massA)
    (sourceOriginalActualPrimitiveGlobalKernel434 Q JB hB massB)
    DA DB r XA XB (Q:ℝ) xi (Nat.cast_nonneg _) hxi
    hAchar hBchar u v
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimitiveModeKnuFactor -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The TRUE SOURCE03 D-side mode of one global primitive
character and one actual half-open GLOBAL log-product cell.
It depends ONLY on the auxiliary marked prime product D,
even if the test eventually paired against it is arbitrary. -/
noncomputable def sourceOriginalPrimitiveInputCellMode434
    (Q : ℕ) (h : ℝ) (j : ℤ)
    (c : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (D : ℕ) : ℂ :=
  if sourceOriginalLiteralLogCell434 h j D
  then star (c.2 (D:ZMod (c.1.val+1)))
  else 0

/-- The TRUE SOURCE03 X-side coefficient; this is EXACTLY
chi(X)/nu_j with the matching original retained-cell
gate, no faux independent integer product probability. -/
noncomputable def sourceOriginalPrimitiveOutputCellCoefficient434
    (Q : ℕ) (h : ℝ) (mass : ℤ → ℝ) (j : ℤ)
    (c : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (X : ℕ) : ℂ :=
  if sourceOriginalLiteralLogCell434 h j X
  then ((mass j:ℂ)⁻¹)*c.2 (X:ZMod (c.1.val+1))
  else 0
/-- EXACT physical factorization of the SOURCE03 primitive
GLOBAL cell atom into a D-only input and a X-only output,
including the source's complex conjugation orientation. -/
theorem source_original_primitive_cell_atom_input_output434
    (Q : ℕ) (h : ℝ) (mass : ℤ → ℝ) (j : ℤ)
    (c : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (D X : ℕ) :
    sourceOriginalCharacterCellAtom434
      (sourceOriginalLiteralLogCell434 h) mass
      (fun c n => c.2 (n:ZMod (c.1.val+1)))
      j c D X =
    sourceOriginalPrimitiveOutputCellCoefficient434
      Q h mass j c X *
    sourceOriginalPrimitiveInputCellMode434 Q h j c D := by
  classical
  by_cases hD : sourceOriginalLiteralLogCell434 h j D
  · by_cases hX : sourceOriginalLiteralLogCell434 h j X
    · simp only [
        sourceOriginalCharacterCellAtom434,
        sourceOriginalPrimitiveOutputCellCoefficient434,
        sourceOriginalPrimitiveInputCellMode434,
        hD,hX, and_self, if_pos]
      ring
    · simp [sourceOriginalCharacterCellAtom434,
         sourceOriginalPrimitiveOutputCellCoefficient434,
         sourceOriginalPrimitiveInputCellMode434,hD,hX]
  · simp [sourceOriginalCharacterCellAtom434,
      sourceOriginalPrimitiveOutputCellCoefficient434,
      sourceOriginalPrimitiveInputCellMode434,hD]
/-- The ORIGINAL signed source03 ν pattern Knu is exactly
a FOURFOLD sum: GLOBAL A-cell, primitive A-character,
GLOBAL B-cell, primitive B-character. EACH summand factors
into the product of a physical D_A-only mode and a
physical D_B-only mode, times explicit endpoint-only
coefficients at X_A,X_B and exact -(-1)^r.
This is the direct algebraic interface needed to apply
the source03 true-ν BIG/BIG minor estimate C275 separately
to every primitive mode, WITHOUT imposing independence
of original endpoint test functions. -/
theorem source_original_actual_primitive_Knu_minor_mode_expand434
    (Q : ℕ) (JA JB : Finset ℤ) (hA hB : ℝ)
    (massA massB : ℤ → ℝ)
    (DA XA DB XB r : ℕ) :
    sourceOriginalActualPrimitiveComparisonKernel434
      Q JA JB hA hB massA massB DA XA DB XB r =
    ∑ jA ∈ JA,
      ∑ cA ∈ sourceOriginalActualPrimitiveCharacters434 Q,
        ∑ jB ∈ JB,
          ∑ cB ∈ sourceOriginalActualPrimitiveCharacters434 Q,
            -((-1:ℂ)^r) *
            (sourceOriginalPrimitiveOutputCellCoefficient434
              Q hA massA jA cA XA *
             sourceOriginalPrimitiveOutputCellCoefficient434
              Q hB massB jB cB XB) *
            (sourceOriginalPrimitiveInputCellMode434
              Q hA jA cA DA *
             sourceOriginalPrimitiveInputCellMode434
              Q hB jB cB DB) := by
  classical
  rw [source_original_actual_primitive_comparison_expand434]
  apply Finset.sum_congr rfl
  intro jA hjA
  apply Finset.sum_congr rfl
  intro cA hcA
  apply Finset.sum_congr rfl
  intro jB hjB
  apply Finset.sum_congr rfl
  intro cB hcB
  rw [source_original_primitive_cell_atom_input_output434,
      source_original_primitive_cell_atom_input_output434]
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalGlobalModes -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- The genuine SOURCE03 global primitive-character
comparison frame, on the ACTUAL prime products D and X,
factors exactly as a single sum over PAIRS
(j,primitive-character) of an X-only coefficient and a
D-only mode. All original conductors and cell masses are
retained; this is a finite algebraic equality, not a
norm estimate or arbitrary test-factorization claim. -/
theorem source_original_physical_global_character_mode_factor434
    (Q : ℕ) (JA : Finset ℤ)
    (h : ℝ) (mass : ℤ → ℝ) (D X : ℕ) :
    sourceOriginalActualPrimitiveGlobalKernel434
      Q JA h mass D X =
    ∑ jc ∈ JA.product (sourceOriginalActualPrimitiveCharacters434 Q),
      sourceOriginalPrimitiveOutputCellCoefficient434
        Q h mass jc.1 jc.2 X *
      sourceOriginalPrimitiveInputCellMode434
        Q h jc.1 jc.2 D := by
  classical
  unfold sourceOriginalActualPrimitiveGlobalKernel434
  rw [source_original_character_cell_kernel_expand434]
  rw [← Finset.sum_product']
  apply Finset.sum_congr rfl
  intro jc hjc
  exact source_original_primitive_cell_atom_input_output434
    Q h mass jc.1 jc.2 D X
/-- EXACT original signed two-global SOURCE03 Knu
kernel has a separated D_A/D_B expansion over the TWO
true finite sets of (GLOBAL-cell, primitive character)
pairs. It is valid for arbitrary (D_A,X_A,D_B,X_B)
and true cell weights, and records the literal
inclusion-exclusion sign -(-1)^r. -/
theorem source_original_original_signed_Knu_separated_modes434
    (Q : ℕ) (JA JB : Finset ℤ)
    (hA hB : ℝ) (massA massB : ℤ → ℝ)
    (DA XA DB XB r : ℕ) :
    sourceOriginalActualPrimitiveComparisonKernel434
      Q JA JB hA hB massA massB DA XA DB XB r =
      -((-1:ℂ)^r) *
      (∑ jc ∈ JA.product (sourceOriginalActualPrimitiveCharacters434 Q),
        sourceOriginalPrimitiveOutputCellCoefficient434
          Q hA massA jc.1 jc.2 XA *
        sourceOriginalPrimitiveInputCellMode434
          Q hA jc.1 jc.2 DA) *
      (∑ jc ∈ JB.product (sourceOriginalActualPrimitiveCharacters434 Q),
        sourceOriginalPrimitiveOutputCellCoefficient434
          Q hB massB jc.1 jc.2 XB *
        sourceOriginalPrimitiveInputCellMode434
          Q hB jc.1 jc.2 DB) := by
  unfold sourceOriginalActualPrimitiveComparisonKernel434
  rw [source_original_physical_global_character_mode_factor434,
      source_original_physical_global_character_mode_factor434]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbePhysicalBudget -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The ORIGINAL signed, physically projected two-global-kernel
comparison coefficient, with its pattern-dependent free-slot counts
and separately evaluated target/source mark products. -/
noncomputable def sourceOriginalProbeActualPhysicalKnu434
    {G : Type} [Fintype G] (m Q : ℕ)
    (t : SourceOriginalProbePattern434 G m → G → ℕ)
    (JA JB : SourceOriginalProbePattern434 G m → Finset ℤ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (massA massB : SourceOriginalProbePattern434 G m → ℤ → ℝ)
    (DA DB r : SourceOriginalProbePattern434 G m → ℕ)
    (XA XB : (ν : SourceOriginalProbePattern434 G m) →
      (∀ g,Fin (t ν g) → ℕ) → ℕ)
    (source target : (ν : SourceOriginalProbePattern434 G m) →
      ∀ g,Fin (t ν g) → ℕ)
    (ν : SourceOriginalProbePattern434 G m) : ℂ :=
  sourceAuxiliaryOriginalComparisonKnu434 (t ν)
    (sourceOriginalActualPrimitiveGlobalKernel434 Q (JA ν) (hA ν) (massA ν))
    (sourceOriginalActualPrimitiveGlobalKernel434 Q (JB ν) (hB ν) (massB ν))
    (DA ν) (DB ν) (r ν)
    (XA ν) (XB ν) (source ν) (target ν)

/-- Total physical signed comparison coefficient, for the EXACT
source03 residual probe enumeration, without assuming an external
cost bound for the family. Both primitive character kernels are
literal source03 objects. At this stage the slot-to-mark projections
are supplied per pattern; the groupwise geometry is addressed by the
separate original physical-state modules. -/
theorem source_original_probe_actual_physical_family_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (blockA blockB : Finset G) (m Q : ℕ) (xi : ℝ)
    (hxi : 0 < xi)
    (t : SourceOriginalProbePattern434 G m → G → ℕ)
    (JA JB : SourceOriginalProbePattern434 G m → Finset ℤ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 < hA ν)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 < hB ν)
    (massA massB : SourceOriginalProbePattern434 G m → ℤ → ℝ)
    (hMassA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      ∀ j ∈ JA ν,xi ≤ massA ν j)
    (hMassB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      ∀ j ∈ JB ν,xi ≤ massB ν j)
    (DA DB r : SourceOriginalProbePattern434 G m → ℕ)
    (XA XB : (ν : SourceOriginalProbePattern434 G m) →
      (∀ g,Fin (t ν g) → ℕ) → ℕ)
    (source target : (ν : SourceOriginalProbePattern434 G m) →
      ∀ g,Fin (t ν g) → ℕ) :
    (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      ‖sourceOriginalProbeActualPhysicalKnu434 m Q t JA JB hA hB
        massA massB DA DB r XA XB source target ν‖) ≤
    (2 ^ (m*(blockA.card+blockB.card)):ℝ) *
      ((Q:ℝ)^4*(xi⁻¹)^2) := by
  let patterns := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let B : ℝ := (Q:ℝ)^4*(xi⁻¹)^2
  have hCap : 0 ≤ B := by
    dsimp [B]
    positivity
  have hPointwise (ν : SourceOriginalProbePattern434 G m)
      (hν : ν ∈ patterns) :
      ‖sourceOriginalProbeActualPhysicalKnu434 m Q t JA JB hA hB
        massA massB DA DB r XA XB source target ν‖ ≤ B := by
    exact source_original_actual_primitive_physical_Knu_bound434
      (t ν) Q xi hxi
      (JA ν) (JB ν) (hA ν) (hB ν)
      (hhA ν hν) (hhB ν hν)
      (massA ν) (massB ν)
      (hMassA ν hν) (hMassB ν hν)
      (DA ν) (DB ν) (r ν)
      (XA ν) (XB ν) (source ν) (target ν)
  have hCardNat := source_original_two_block_probe_pattern_card434
    blockA blockB m
  have hCard :
      (patterns.card:ℝ) ≤ (2 ^ (m*(blockA.card+blockB.card)):ℝ) := by
    exact_mod_cast hCardNat
  calc
    _ ≤ ∑ ν ∈ patterns,B := by
      apply Finset.sum_le_sum
      intro ν hν
      exact hPointwise ν hν
    _ = (patterns.card:ℝ)*B := by simp [Finset.sum_const]
    _ ≤ (2 ^ (m*(blockA.card+blockB.card)):ℝ)*B :=
      mul_le_mul_of_nonneg_right hCard hCap
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTruePrimitivePhysicalExpectationExpansion -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Exact original SOURCE03 primitive-Knu Fourier/Mellin
expansion INSIDE the genuine auxiliary expectation.
All two GLOBAL jA/χA, jB/χB indices are genuine primitive
characters, and the fully coupled product phase remains
inside the auxiliary prime-law expectation. No artificial
factorization, new signs or analytic bounds. -/
theorem source_original_true_primitive_physical_expectation_expand434
    {Aux : Type} [Fintype Aux]
    (Q : ℕ) (JA JB : Finset ℤ)
    (hA hB : ℝ) (massA massB : ℤ → ℝ)
    (DA DB : Aux → ℕ) (XA XB r : ℕ)
    (weight : Aux → ℂ) (phase : ℕ → ℂ) :
    let Char := sourceOriginalActualPrimitiveCharacters434 Q
    let Modes := ((JA.product Char).product (JB.product Char))
    let kernel := fun z : ((ℤ ×
      (Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))) ×
      (ℤ × (Σ q : Fin Q, DirichletCharacter ℂ (q.val+1)))) =>
      fun a : Aux =>
        -((-1:ℂ)^r) *
          sourceOriginalCharacterCellAtom434
            (sourceOriginalLiteralLogCell434 hA) massA
            (fun c n => c.2 (n:ZMod (c.1.val+1)))
            z.1.1 z.1.2 (DA a) XA *
          sourceOriginalCharacterCellAtom434
            (sourceOriginalLiteralLogCell434 hB) massB
            (fun c n => c.2 (n:ZMod (c.1.val+1)))
            z.2.1 z.2.2 (DB a) XB
    (∑ a : Aux,
       weight a * sourceOriginalActualPrimitiveComparisonKernel434
         Q JA JB hA hB massA massB
         (DA a) XA (DB a) XB r * phase (DA a*DB a)) =
    ∑ mode ∈ Modes,
       ∑ a : Aux, weight a * kernel mode a * phase (DA a*DB a) := by
  classical
  let Char := sourceOriginalActualPrimitiveCharacters434 Q
  let Modes := ((JA.product Char).product (JB.product Char))
  let kernel := fun z : ((ℤ ×
      (Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))) ×
      (ℤ × (Σ q : Fin Q, DirichletCharacter ℂ (q.val+1)))) =>
    fun a : Aux =>
      -((-1:ℂ)^r) *
        sourceOriginalCharacterCellAtom434
          (sourceOriginalLiteralLogCell434 hA) massA
          (fun c n => c.2 (n:ZMod (c.1.val+1)))
          z.1.1 z.1.2 (DA a) XA *
        sourceOriginalCharacterCellAtom434
          (sourceOriginalLiteralLogCell434 hB) massB
          (fun c n => c.2 (n:ZMod (c.1.val+1)))
          z.2.1 z.2.2 (DB a) XB
  have hKernel (a : Aux) :
      sourceOriginalActualPrimitiveComparisonKernel434
        Q JA JB hA hB massA massB
          (DA a) XA (DB a) XB r =
      ∑ z ∈ Modes, kernel z a := by
    have hh := source_original_actual_primitive_comparison_expand434
      Q JA JB hA hB massA massB (DA a) XA (DB a) XB r
    simpa only [Modes,Char,kernel,Finset.product_eq_sprod,
      Finset.sum_product] using hh
  change (∑ a : Aux,
       weight a * sourceOriginalActualPrimitiveComparisonKernel434
         Q JA JB hA hB massA massB
         (DA a) XA (DB a) XB r * phase (DA a*DB a)) =
    ∑ z ∈ Modes,
       ∑ a : Aux, weight a * kernel z a * phase (DA a*DB a)
  calc
    _ = ∑ a : Aux, ∑ z ∈ Modes,
       weight a * kernel z a * phase (DA a*DB a) := by
         apply Finset.sum_congr rfl
         intro a ha
         rw [hKernel a]
         simp only [Finset.mul_sum,Finset.sum_mul]
    _ = _ := Finset.sum_comm
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteActiveLogCells -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- The actual integer index of the unique source03 half-open
logarithmic cell [jh,(j+1)h) containing the complete product D. -/
noncomputable def sourceOriginalLiteralLogCellIndex434
    (h : ℝ) (D : ℕ) : ℤ := ⌊Real.log (D:ℝ)/h⌋

theorem source_original_literal_log_cell_index_mem434
    (h : ℝ) (hh : 0 < h) (D : ℕ) :
    sourceOriginalLiteralLogCell434 h
      (sourceOriginalLiteralLogCellIndex434 h D) D := by
  let y : ℝ := Real.log (D:ℝ)/h
  have hflo : (⌊y⌋:ℝ) ≤ y := Int.floor_le y
  have hfhi : y < ((⌊y⌋:ℤ):ℝ)+1 := Int.lt_floor_add_one y
  have hlo : ((⌊y⌋:ℤ):ℝ)*h ≤ Real.log (D:ℝ) := by
    exact (le_div_iff₀ hh).mp hflo
  have hhi : Real.log (D:ℝ) < (((⌊y⌋:ℤ):ℝ)+1)*h := by
    exact (div_lt_iff₀ hh).mp hfhi
  exact ⟨hlo,hhi⟩

theorem source_original_literal_log_cell_iff_index434
    (h : ℝ) (hh : 0 < h) (D : ℕ) (j : ℤ) :
    sourceOriginalLiteralLogCell434 h j D ↔
      j=sourceOriginalLiteralLogCellIndex434 h D := by
  constructor
  · intro hj
    exact source_original_literal_log_cells_unique434
      h hh D j _ hj (source_original_literal_log_cell_index_mem434 h hh D)
  · rintro rfl
    exact source_original_literal_log_cell_index_mem434 h hh D

/-- Unlike an artificial bounded Z-window, these are EXACTLY the
log-cell indices that can occur in the FINITE true independent
labelled source product law. Other empty-product cells are absent. -/
noncomputable def sourceOriginalCandidateLogCells434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (h : ℝ) : Finset ℤ :=
  (Fintype.piFinset S).image
    (fun a => sourceOriginalLiteralLogCellIndex434 h (∏ i : ι,a i))

/-- SOURCE03 finite active cells are precisely the actual cells
whose full independent-prime-product probability is at least xi. -/
noncomputable def sourceOriginalFiniteActiveLogCells434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h xi : ℝ) : Finset ℤ :=
  (sourceOriginalCandidateLogCells434 S h).filter
    (fun j => xi ≤ sourceOriginalActualCellProbability434 S mu h j)

/-- Every state with an admissible source product belongs to the
corresponding finite candidate cell; no primitive/positive-prime
hypotheses are needed for the combinatorial cell indexing. -/
theorem source_original_candidate_log_cells_complete434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (h : ℝ) (hh : 0 < h)
    (a : ι → ℕ) (ha : a ∈ Fintype.piFinset S)
    (j : ℤ) (hj : sourceOriginalLiteralLogCell434 h j (∏ i : ι,a i)) :
    j ∈ sourceOriginalCandidateLogCells434 S h := by
  classical
  have hidx : j=sourceOriginalLiteralLogCellIndex434 h (∏ i : ι,a i) :=
    (source_original_literal_log_cell_iff_index434 h hh _ j).mp hj
  exact Finset.mem_image.mpr ⟨a,ha,hidx.symm⟩

/-- A cell absent from the finite candidate set has ACTUAL source
probability zero, not merely negligible probability. -/
theorem source_original_outside_candidate_probability_zero434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (hh : 0 < h) (j : ℤ)
    (hj : j ∉ sourceOriginalCandidateLogCells434 S h) :
    sourceOriginalActualCellProbability434 S mu h j=0 := by
  classical
  unfold sourceOriginalActualCellProbability434
  apply Finset.sum_eq_zero
  intro a ha
  have hc : ¬sourceOriginalLiteralLogCell434 h j (∏ i : ι,a i) :=
    fun hc => hj (source_original_candidate_log_cells_complete434 S h hh a ha j hc)
  simp only [if_neg hc]

/-- IMPORTANT: exact ⇔, with NO assumed externally truncated
range of cells, and no bogus positive-cell premise inserted.
Every actual active ν_j≥xi is in the finite selected family. -/
theorem source_original_finite_active_log_cell_mem_iff434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h xi : ℝ) (hh : 0 < h) (hxi : 0 < xi) (j : ℤ) :
    j ∈ sourceOriginalFiniteActiveLogCells434 S mu h xi ↔
      xi ≤ sourceOriginalActualCellProbability434 S mu h j := by
  classical
  constructor
  · intro hj
    exact (Finset.mem_filter.mp hj).2
  · intro hj
    have hIn : j ∈ sourceOriginalCandidateLogCells434 S h := by
      by_contra hc
      have hz := source_original_outside_candidate_probability_zero434
        S mu h hh j hc
      rw [hz] at hj
      exact (not_le_of_gt hxi) hj
    exact Finset.mem_filter.mpr ⟨hIn,hj⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalCandidateLogCellCard -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The FINITE genuine source03 candidate log-cell family has
at most ceil(U/h)+1 members when all the original independently
labelled prime products are positive and satisfy log D <= U.
The bound is independent of the size of the prime supports:
one possible integer j for each unit interval in log D / h,
with no fake finite cell window or invented probabilities. -/
theorem source_original_candidate_log_cells_card_le_upper434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (h U : ℝ)
    (hh : 0 < h)
    (hPos : ∀ a ∈ Fintype.piFinset S,
       1 ≤ (∏ i : ι, a i))
    (hUpper : ∀ a ∈ Fintype.piFinset S,
       Real.log (((∏ i : ι, a i):ℕ):ℝ) ≤ U) :
    (sourceOriginalCandidateLogCells434 S h).card ≤
      Nat.ceil (U/h)+1 := by
  classical
  let C : Finset ℤ := sourceOriginalCandidateLogCells434 S h
  let R : Finset ℤ :=
    (Finset.range (Nat.ceil (U/h)+1)).image (fun k : ℕ => (k:ℤ))
  have hSub : C ⊆ R := by
    intro j hj
    have hj' : j ∈ (Fintype.piFinset S).image
       (fun a => sourceOriginalLiteralLogCellIndex434 h
         (∏ i : ι, a i)) := hj
    obtain ⟨a,ha,haj⟩ := Finset.mem_image.mp hj'
    let D : ℕ := ∏ i : ι, a i
    have hP : (1:ℝ) ≤ (D:ℝ) := by
      exact_mod_cast hPos a ha
    have hLog0 : 0 ≤ Real.log (D:ℝ) :=
      Real.log_nonneg hP
    have hDiv0 : 0 ≤ Real.log (D:ℝ)/h :=
      div_nonneg hLog0 hh.le
    have hj0 : 0 ≤ j := by
      rw [←haj]
      exact Int.floor_nonneg.mpr hDiv0
    have hjLe : (j:ℝ) ≤ U/h := by
      rw [←haj]
      exact (Int.floor_le _).trans
        (div_le_div_of_nonneg_right (hUpper a ha) hh.le)
    have hToNat : (j.toNat:ℝ) ≤ (Nat.ceil (U/h):ℝ) := by
      have hjEqual : (j.toNat:ℝ)=(j:ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hj0
      calc
        _ = (j:ℝ) := hjEqual
        _ ≤ U/h := hjLe
        _ ≤ (Nat.ceil (U/h):ℝ) := Nat.le_ceil _
    have hNat : j.toNat ≤ Nat.ceil (U/h) := by
      exact_mod_cast hToNat
    refine Finset.mem_image.mpr ⟨j.toNat,
      Finset.mem_range.mpr (by omega), ?_⟩
    exact Int.toNat_of_nonneg hj0
  calc
    _ = C.card := rfl
    _ ≤ R.card := Finset.card_le_card hSub
    _ ≤ (Finset.range (Nat.ceil (U/h)+1)).card :=
      Finset.card_image_le
    _ = Nat.ceil (U/h)+1 := Finset.card_range _
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualCandidateCellGeometry -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- The original actual product of independently labelled BIG
primes with 1<=p<=Bmax has only O(m log(Bmax)/h) attainable
half-open GLOBAL logarithmic cells, where m is the TRUE
number of labelled slots. This is a real logarithmic geometry
bound, independent of the exponentially large number of
possible prime combinations and allowing repeated prime values.
No candidate cell count assumption is introduced. -/
theorem source_original_candidate_log_cells_card_by_prime_support434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (h Bmax : ℝ)
    (hh : 0 < h) (hB : 1 ≤ Bmax)
    (hMin : ∀ i p, p ∈ S i → 1 ≤ p)
    (hMax : ∀ i p, p ∈ S i → (p:ℝ) ≤ Bmax) :
    (sourceOriginalCandidateLogCells434 S h).card ≤
      Nat.ceil (((Fintype.card ι:ℝ)*Real.log Bmax)/h)+1 := by
  classical
  have hPos (a : ι → ℕ) (ha : a ∈ Fintype.piFinset S) :
      1 ≤ ∏ i : ι, a i := by
    apply Finset.one_le_prod
    intro i hi
    exact hMin i (a i) ((Fintype.mem_piFinset.mp ha) i)
  have hUpper (a : ι → ℕ) (ha : a ∈ Fintype.piFinset S) :
      Real.log (((∏ i : ι, a i):ℕ):ℝ) ≤
        (Fintype.card ι:ℝ)*Real.log Bmax := by
    have hs (i : ι) :
        0 < (a i:ℝ) := by
      have hh := hMin i (a i) ((Fintype.mem_piFinset.mp ha) i)
      exact_mod_cast (by omega : 0 < a i)
    have hlog (i : ι) :
        Real.log (a i:ℝ) ≤ Real.log Bmax :=
      Real.log_le_log (hs i)
        (hMax i (a i) ((Fintype.mem_piFinset.mp ha) i))
    calc
      _ = ∑ i : ι, Real.log (a i:ℝ) := by
        rw [Nat.cast_prod, Real.log_prod]
        intro i hi
        exact (hs i).ne'
      _ ≤ ∑ _i : ι, Real.log Bmax :=
        Finset.sum_le_sum (fun i hi => hlog i)
      _ = (Fintype.card ι:ℝ)*Real.log Bmax := by simp
  exact source_original_candidate_log_cells_card_le_upper434
    S h ((Fintype.card ι:ℝ)*Real.log Bmax) hh hPos hUpper
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalLogCellComparison -/

section

open MeasureTheory Filter
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64SourceC6 Green64Analytic.CorrelationMellin
set_option maxHeartbeats 18000000

/-- Genuine SOURCE log-cell expectations in FOUR independent parity channels.
All endpoint-energy, first-endpoint arc, and multiplier bounds are PROVED,
not hypotheses. Only original coefficient discrepancy is required, and only
for the first endpoint. The marked functions, physical Y, product shifts,
probability normalizations, and shared-label phase are unchanged. -/
theorem eventually_source_original_logcell_comparison434
    (cfg : SourceComparisonFixed434)
    (dexp Aarc Bsave C1 C2 Chigh Cprod vprod Ck D : ℝ) (m0 : ℕ)
    (hd : 0 ≤ dexp) (hdA : dexp < Aarc) (hB : 0 ≤ Bsave)
    (hCarc : Aarc+Bsave ≤ cfg.Carc) (hChigh : 0 ≤ Chigh)
    (hvprod : 0 < vprod) (hCprod : 0 ≤ Cprod) (hCk : 0 ≤ Ck)
    (hDenExponent : Ck+Bsave+1 ≤ (cfg.cm:ℝ))
    (hChoice : 2*(Cprod*Real.log ((Nat.factorial m0:ℝ)*
      (max (1:ℝ) vprod⁻¹)^m0)+D+source_data_global_exponent434 cfg) ≤ Bsave) :
    ∃ Kout : ℝ, 0 ≤ Kout ∧ ∃ B : ℕ, ∃ X0 : ℝ, 3 ≤ X0 ∧
      ∀ᶠ L : ℝ in atTop, ∀ x : ℝ, X0 ≤ x → L = Real.log x → 3 ≤ L →
      ∀ {γ₁ γ₂ : Type} [DecidableEq γ₁] [DecidableEq γ₂]
        (G₁ : Finset γ₁) (S₁ : γ₁ → Finset ℕ) (k₁ : γ₁ → ℕ) (V₁ : γ₁ → ℝ)
        (G₂ : Finset γ₂) (S₂ : γ₂ → Finset ℕ) (k₂ : γ₂ → ℕ) (V₂ : γ₂ → ℝ),
      (∀ g ∈ G₁, ∀ p ∈ S₁ g, Nat.Prime p) →
      (∀ g ∈ G₂, ∀ p ∈ S₂ g, Nat.Prime p) →
      (∀ g ∈ G₁, ∀ h ∈ G₁, g ≠ h → Disjoint (S₁ g) (S₁ h)) →
      (∀ g ∈ G₂, ∀ h ∈ G₂, g ≠ h → Disjoint (S₂ g) (S₂ h)) →
      (∀ g ∈ G₁, V₁ g = ∑ p ∈ S₁ g, 1/(p:ℝ)) →
      (∀ g ∈ G₂, V₂ g = ∑ p ∈ S₂ g, 1/(p:ℝ)) →
      (∀ g ∈ G₁, k₁ g ≤ m0) → (∀ g ∈ G₂, k₂ g ≤ m0) →
      (∀ g ∈ G₁, vprod ≤ V₁ g) → (∀ g ∈ G₂, vprod ≤ V₂ g) →
      (G₁.card:ℝ) ≤ Cprod*Real.log L → (G₂.card:ℝ) ≤ Cprod*Real.log L →
      ∀ (U1 U2 : ℝ),
      Real.exp (L^cfg.cexp-C1) ≤ U1 → Real.exp (L^cfg.cexp-C2) ≤ U2 →
      U1*U2 ≤ Real.exp (Chigh*Real.log L*L^dexp) →
      ∀ (F1 F2 : Finset ℕ) (width1 width2 : ℝ), width1 ≤ 1 → width2 ≤ 1 →
      ∀ (b₁ b₂ : ℕ → ℂ),
      (∀ n ∈ F1, ‖b₁ n‖ ≤ 1) → (∀ n ∈ F2, ‖b₂ n‖ ≤ 1) →
      ∀ (k : ℤ), k ≠ 0 → (k.natAbs:ℝ) ≤ L^Ck →
      ∀ (Y : ℝ) {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
        (u v : SourceComparisonData434 ι β cfg x L Y (U1*U2)),
      SourceAlphaDiscrepancy L (B:ℝ) x u.alpha →
      ∀ (eps1 eps2 : Bool) (sharedSlots : ℕ),
      ‖((if eps1 then (-1:ℂ)^sharedSlots else 1)*
          (if eps2 then (-1:ℂ)^sharedSlots else 1)) *
        (∑ da ∈ F1, (sourceProductAtomMass G₁ S₁ k₁ V₁ da:ℂ)*
          sourceOriginalLogCellMask434 F1 U1 width1 b₁ da *
          (∑ db ∈ F2, (sourceProductAtomMass G₂ S₂ k₂ V₂ db:ℂ)*
            sourceOriginalLogCellMask434 F2 U2 width2 b₂ db *
            (∑ m ∈ u.support, ∑ n ∈ v.support,
              if n = m+k*(da:ℤ)*(db:ℤ) then
                star (sourceSignedCoefficients434 u.Ptw eps1 u.endpoint m)*
                  sourceSignedCoefficients434 u.Ptw eps2 v.endpoint n else 0)))‖ ≤
          Kout*Y*L^(-D) := by
  obtain ⟨Kout,hKout,B,X0,hX0,hComp⟩ :=
    eventually_source_original_four_channel_comparison434 cfg dexp Aarc Bsave C1 C2 Chigh
      Cprod vprod Ck D m0 hd hdA hB hCarc hChigh hvprod hCprod hCk hDenExponent hChoice
  refine ⟨Kout,hKout,B,X0,hX0,?_⟩
  filter_upwards [hComp] with L hCompL
  intro x hx hLog hL γ₁ γ₂ _ _ G₁ S₁ k₁ V₁ G₂ S₂ k₂ V₂
    hp₁ hp₂ hd₁ hd₂ hV₁exact hV₂exact hk₁ hk₂ hV₁ hV₂ hcard₁ hcard₂
    U1 U2 hMscale hNscale hHigh F1 F2 width1 width2 hw1 hw2 b₁ b₂ hb₁ hb₂
    k hk hKshift Y ι β _ _ _ _ u v hDisc eps1 eps2 sharedSlots
  have hU1 : 0 < U1 := (Real.exp_pos _).trans_le hMscale
  have hU2 : 0 < U2 := (Real.exp_pos _).trans_le hNscale
  let b1 := sourceOriginalLogCellMask434 F1 U1 width1 b₁
  let b2 := sourceOriginalLogCellMask434 F2 U2 width2 b₂
  have hBound := hCompL x hx hLog hL G₁ S₁ k₁ V₁ G₂ S₂ k₂ V₂
    hp₁ hp₂ hd₁ hd₂ hV₁exact hV₂exact hk₁ hk₂ hV₁ hV₂ hcard₁ hcard₂
    (Nat.ceil U1) (Nat.ceil U2) (Nat.ceil_pos.mpr hU1) (Nat.ceil_pos.mpr hU2)
    U1 U2 hMscale hNscale (Nat.le_ceil U1) (Nat.le_ceil U2) hHigh b1 b2
    (fun n hn => source_original_logcell_mask_norm434 F1 U1 width1 b₁ hb₁ n)
    (fun n hn => source_original_logcell_mask_norm434 F2 U2 width2 b₂ hb₂ n)
    k hk hKshift Y u v hDisc eps1 eps2 sharedSlots
  have hEq := source_original_logcell_product_reindex434 F1 F2 U1 U2 width1 width2 b₁ b₂
    (sourceProductAtomMass G₁ S₁ k₁ V₁) (sourceProductAtomMass G₂ S₂ k₂ V₂)
    (fun da db => ∑ m ∈ u.support, ∑ n ∈ v.support,
      if n = m+k*(da:ℤ)*(db:ℤ) then
        star (sourceSignedCoefficients434 u.Ptw eps1 u.endpoint m)*
          sourceSignedCoefficients434 u.Ptw eps2 v.endpoint n else 0)
    hU1 hU2 hw1 hw2
  rw [hEq]
  exact hBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalMinorOutputCoeffNorm -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- For every ACTUAL primitive source03 character and
original retained GLOBAL log-cell, the output coefficient
chi(X)/nu_j has norm at most nu_j^-1. The target X is
arbitrary, even if the character vanishes there; no
primality/coprimality or character-independence assumption. -/
theorem source_original_primitive_output_cell_norm_le_inv_mass434
    (Q : ℕ) (h : ℝ) (mass : ℤ → ℝ)
    (j : ℤ) (c : Σ q : Fin Q,
       DirichletCharacter ℂ (q.val+1))
    (X : ℕ) (hMass : 0 < mass j) :
    ‖sourceOriginalPrimitiveOutputCellCoefficient434
       Q h mass j c X‖ ≤ (mass j)⁻¹ := by
  classical
  unfold sourceOriginalPrimitiveOutputCellCoefficient434
  by_cases hc : sourceOriginalLiteralLogCell434 h j X
  · simp only [if_pos hc,norm_mul,norm_inv,
        Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos hMass]
    exact (mul_le_mul_of_nonneg_left
      (c.2.norm_le_one _) (inv_nonneg.mpr hMass.le)).trans_eq
        (mul_one _)
  · simp only [if_neg hc,norm_zero]
    exact inv_nonneg.mpr hMass.le

/-- EXACT source ν-pattern sign contributes NO
additional loss to the two-primitive-mode cost:
| -(-1)^r a_i b_j | ≤ nu_A^-1 nu_B^-1.
The independent output-character phases never require
an exogenous L∞ coefficient bound. -/
theorem source_original_signed_primitive_output_pair_norm434
    (Q r : ℕ) (hA hB : ℝ)
    (massA massB : ℤ → ℝ)
    (jA jB : ℤ)
    (cA cB : Σ q : Fin Q,
        DirichletCharacter ℂ (q.val+1))
    (XA XB : ℕ)
    (hMassA : 0 < massA jA)
    (hMassB : 0 < massB jB) :
    ‖(-((-1:ℂ)^r))*
       sourceOriginalPrimitiveOutputCellCoefficient434
         Q hA massA jA cA XA *
       sourceOriginalPrimitiveOutputCellCoefficient434
         Q hB massB jB cB XB‖ ≤
       (massA jA)⁻¹*(massB jB)⁻¹ := by
  have hA0 := source_original_primitive_output_cell_norm_le_inv_mass434
    Q hA massA jA cA XA hMassA
  have hB0 := source_original_primitive_output_cell_norm_le_inv_mass434
    Q hB massB jB cB XB hMassB
  have hNN : 0 ≤ (massA jA)⁻¹ :=
    inv_nonneg.mpr hMassA.le
  have hNNB : 0 ≤ (massB jB)⁻¹ :=
    inv_nonneg.mpr hMassB.le
  have hMul :
      ‖sourceOriginalPrimitiveOutputCellCoefficient434
        Q hA massA jA cA XA‖ *
      ‖sourceOriginalPrimitiveOutputCellCoefficient434
        Q hB massB jB cB XB‖ ≤
      (massA jA)⁻¹*(massB jB)⁻¹ :=
    mul_le_mul hA0 hB0 (norm_nonneg _) hNN
  simpa only [norm_mul,norm_neg,norm_pow,norm_neg,norm_one,
    one_pow,one_mul] using hMul
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimitiveFrameSize -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false

/-- The actual finite original primitive family has at most Q² labels.
This converts the literal source Q-level primitive count to the
subtype Fintype cardinality in the physical Gram frame. -/
theorem source_original_primitive_frame_card_le_square434
    (Q : ℕ) :
    Fintype.card
      {c : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1) //
         c ∈ sourceOriginalActualPrimitiveCharacters434 Q} ≤ Q^2 := by
  classical
  have h :
      Fintype.card
        {c : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1) //
           c ∈ sourceOriginalActualPrimitiveCharacters434 Q} =
      (sourceOriginalActualPrimitiveCharacters434 Q).card := by
    change Fintype.card
      {c : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1) //
        c ∈ sourceOriginalActualPrimitiveCharacters434 Q} = _
    rw [Fintype.card_subtype]
    simp
  rw [h]
  exact source_original_actual_primitive_count434 Q
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeAuxiliaryLaw -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- For a specific original comparison pattern, the auxiliary
coordinates are EXACTLY the independently freed A and B probe
positions, not all J marks or a common fixed index type. -/
abbrev SourceOriginalProbeAuxIndex434
    {G : Type} (m : ℕ) (ν : SourceOriginalProbePattern434 G m) :=
  ν.1 ⊕ ν.2

noncomputable def sourceOriginalProbeAuxPrimeSets434
    {G : Type} [DecidableEq G] (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m) (P : G → Finset ℕ) :
    SourceOriginalProbeAuxIndex434 m ν → Finset ℕ :=
  Sum.elim (fun z : ν.1 => P z.val.1) (fun z : ν.2 => P z.val.1)

noncomputable def sourceOriginalProbeAuxV434
    {G : Type} [DecidableEq G] (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m) (V : G → ℝ) :
    SourceOriginalProbeAuxIndex434 m ν → ℝ :=
  Sum.elim (fun z : ν.1 => V z.val.1) (fun z : ν.2 => V z.val.1)

/-- The original two free products, with independent labelled
coordinates and multiplicity even for numerically repeated primes. -/
noncomputable def sourceOriginalProbeDA434
    {G : Type} [DecidableEq G] (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m)
    (a : SourceOriginalProbeAuxIndex434 m ν → ℕ) : ℕ :=
  ∏ z : ν.1, a (Sum.inl z)

noncomputable def sourceOriginalProbeDB434
    {G : Type} [DecidableEq G] (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m)
    (a : SourceOriginalProbeAuxIndex434 m ν → ℕ) : ℕ :=
  ∏ z : ν.2, a (Sum.inr z)

/-- The full auxiliary product is literally D_A*D_B, with
each selected prime slot occurring ONCE even when two numerical
prime values agree. -/
theorem source_original_probe_aux_product_split434
    {G : Type} [DecidableEq G] (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m)
    (a : SourceOriginalProbeAuxIndex434 m ν → ℕ) :
    (∏ z : SourceOriginalProbeAuxIndex434 m ν,a z) =
      sourceOriginalProbeDA434 m ν a*sourceOriginalProbeDB434 m ν a := by
  simp [SourceOriginalProbeAuxIndex434,sourceOriginalProbeDA434,
    sourceOriginalProbeDB434,Fintype.prod_sum_type]

/-- The true source group reciprocal mass is inherited by EVERY
pattern-dependent auxiliary coordinate, without normalization. -/
theorem source_original_probe_aux_V_mass434
    {G : Type} [DecidableEq G] (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g,V g=∑ p ∈ P g,1/(p:ℝ)) :
    ∀ z : SourceOriginalProbeAuxIndex434 m ν,
      sourceOriginalProbeAuxV434 m ν V z =
        ∑ p ∈ sourceOriginalProbeAuxPrimeSets434 m ν P z,1/(p:ℝ) := by
  intro z
  cases z with
  | inl a => exact hV a.val.1
  | inr b => exact hV b.val.1

/-- Genuine product prime measure of the actual source pattern;
the label coordinates may repeat values, not coordinate indices. -/
theorem source_original_probe_aux_law_total434
    {G : Type} [DecidableEq G] (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g,V g=∑ p ∈ P g,1/(p:ℝ))
    (hVp : ∀ g,0 < V g) :
    (∑ a ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m ν P),
      sourceSharedLaw434
        (fun z => sourcePrimeSharedAtom434
          (sourceOriginalProbeAuxV434 m ν V z)) a) = 1 := by
  apply source_shared_law_total434
  intro z
  have hmass := source_original_probe_aux_V_mass434 m ν P V hV z
  have hpos : 0 < sourceOriginalProbeAuxV434 m ν V z := by
    cases z with
    | inl i => exact hVp i.val.1
    | inr j => exact hVp j.val.1
  exact source_prime_shared_atom_total434
    (sourceOriginalProbeAuxPrimeSets434 m ν P z)
    (sourceOriginalProbeAuxV434 m ν V z) hmass hpos.ne'
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeAuxCard -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- Original ν-specific auxiliary index is A ⊕ B, counted with
multiplicities per labelled probe coordinate, independently of J. -/
theorem source_original_probe_aux_card_exact434
    {G : Type} [DecidableEq G] (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m) :
    Fintype.card (SourceOriginalProbeAuxIndex434 m ν) =
      ν.1.card+ν.2.card := by
  simp [SourceOriginalProbeAuxIndex434,Fintype.card_sum,Fintype.card_coe]

/-- The original two nonempty blocks have no more than m probes
per selected big group; no J-dependent auxiliary cardinality. -/
theorem source_original_probe_aux_card_bound434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m)
    (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m) :
    Fintype.card (SourceOriginalProbeAuxIndex434 m ν) ≤
      m*(blockA.card+blockB.card) := by
  classical
  obtain ⟨_,hA,_,hB⟩ :=
    (source_original_two_block_probe_pattern_mem434 blockA blockB m _ _).mp hν
  have hAc := Finset.card_le_card hA
  have hBc := Finset.card_le_card hB
  rw [source_original_probe_aux_card_exact434]
  have hAcount :
      (sourceOriginalProbeBlock434 blockA m).card=blockA.card*m := by
    simp [sourceOriginalProbeBlock434,Finset.card_product,
      Finset.card_univ,Fintype.card_fin]
  have hBcount :
      (sourceOriginalProbeBlock434 blockB m).card=blockB.card*m := by
    simp [sourceOriginalProbeBlock434,Finset.card_product,
      Finset.card_univ,Fintype.card_fin]
  have hle := Nat.add_le_add hAc hBc
  rw [hAcount,hBcount] at hle
  simpa [Nat.mul_add,Nat.mul_comm,
    source_original_probe_aux_card_exact434] using hle

/-- Source03's genuine group-count hypothesis bounds the varying
auxiliary index cardinality by fixed Cs log L, independently of J. -/
theorem source_original_probe_aux_card_log434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m)
    (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (L C0 : ℝ) (hC0 : 0 ≤ C0)
    (hGroups : ((blockA.card+blockB.card:ℕ):ℝ) ≤
      C0*Real.log L) :
    (Fintype.card (SourceOriginalProbeAuxIndex434 m ν):ℝ) ≤
      (m:ℝ)*C0*Real.log L := by
  have hc := source_original_probe_aux_card_bound434
    blockA blockB m ν hν
  have hc' : (Fintype.card (SourceOriginalProbeAuxIndex434 m ν):ℝ) ≤
      (m:ℝ)*((blockA.card+blockB.card:ℕ):ℝ) := by
    exact_mod_cast hc
  calc
    _ ≤ (m:ℝ)*((blockA.card+blockB.card:ℕ):ℝ) := hc'
    _ ≤ (m:ℝ)*(C0*Real.log L) :=
      mul_le_mul_of_nonneg_left hGroups (Nat.cast_nonneg _)
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeTrueDyadPartition -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- For the TRUE ν-dependent physical SOURCE endpoint s, its
selected B-prime product belongs to the candidate family of
genuinely attainable B-product dyads. The physical free positions,
independent group prime supports and original ν selection are all
unchanged. -/
theorem source_original_probe_true_source_dyad_covered434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (s : SourceOriginalVariableBIGState434
       (fun g : G => {p : ℕ // p ∈ P g})
       (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) :
    sourceOriginalLiteralLogCellIndex434 (Real.log (2:ℝ))
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (s g i).val)) ∈
    sourceOriginalCandidateLogCells434
      (fun z : ν.2 => P z.val.1) (Real.log (2:ℝ)) := by
  classical
  let e := sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν
  let f : ν.2 → ℕ := fun z => (s (e z).1 (e z).2).val
  have hf : f ∈ Fintype.piFinset (fun z : ν.2 => P z.val.1) := by
    apply Fintype.mem_piFinset.mpr
    intro z
    exact (s (e z).1 (e z).2).property
  have hp :
      sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
          (fun g i => (s g i).val) = ∏ z : ν.2, f z := by
    rfl
  unfold sourceOriginalCandidateLogCells434
  exact Finset.mem_image.mpr ⟨f,hf,by rw [hp]⟩

/-- True original ν-dependent TARGET endpoint selected
A-prime product also lies in the genuine A-dyad family.
Numerically identical primes at different free positions
remain separately labelled. -/
theorem source_original_probe_true_target_dyad_covered434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (v : SourceOriginalVariableBIGState434
       (fun g : G => {p : ℕ // p ∈ P g})
       (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) :
    sourceOriginalLiteralLogCellIndex434 (Real.log (2:ℝ))
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (v g i).val)) ∈
    sourceOriginalCandidateLogCells434
      (fun z : ν.1 => P z.val.1) (Real.log (2:ℝ)) := by
  classical
  let e := sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν
  let f : ν.1 → ℕ := fun z => (v (e z).1 (e z).2).val
  have hf : f ∈ Fintype.piFinset (fun z : ν.1 => P z.val.1) := by
    apply Fintype.mem_piFinset.mpr
    intro z
    exact (v (e z).1 (e z).2).property
  have hp :
      sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
          (fun g i => (v g i).val) = ∏ z : ν.1, f z := by
    rfl
  unfold sourceOriginalCandidateLogCells434
  exact Finset.mem_image.mpr ⟨f,hf,by rw [hp]⟩
/-- EXACT partition of the FULL original source03 ν-dependent
physical source/target signed BILINEAR sum into all genuinely
attainable PRODUCT-DYAD PAIRS. The original physical variable
free mark lists and true product indices are retained, and
the integrand z may be ANY complex function of the joint
source/target physical prime tuples, including the true
signed RAW-minus-Kν kernel and arbitrary complex endpoint tests.
No disjointness / support cardinal factor is assumed:
unique dyad indices imply the exact Fubini identity. -/
theorem source_original_probe_true_physical_two_ended_dyad_partition434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (z : (SourceOriginalVariableBIGState434
             (fun g : G => {p : ℕ // p ∈ P g})
             (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) ×
         (SourceOriginalVariableBIGState434
             (fun g : G => {p : ℕ // p ∈ P g})
             (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) → ℂ) :
    let X := SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ P g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)
    let CA := sourceOriginalCandidateLogCells434
      (fun z : ν.1 => P z.val.1) (Real.log (2:ℝ))
    let CB := sourceOriginalCandidateLogCells434
      (fun z : ν.2 => P z.val.1) (Real.log (2:ℝ))
    let idxSource : X → ℤ := fun s =>
      sourceOriginalLiteralLogCellIndex434 (Real.log (2:ℝ))
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
          (fun g i => (s g i).val))
    let idxTarget : X → ℤ := fun v =>
      sourceOriginalLiteralLogCellIndex434 (Real.log (2:ℝ))
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
          (fun g i => (v g i).val))
    (∑ ij ∈ CB.product CA,
       ∑ ab : X × X,
         if idxSource ab.1 = ij.1 ∧ idxTarget ab.2 = ij.2
         then z ab else 0) =
    ∑ ab : X × X, z ab := by
  classical
  dsimp only
  let X := SourceOriginalVariableBIGState434
    (fun g : G => {p : ℕ // p ∈ P g})
    (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)
  let CA := sourceOriginalCandidateLogCells434
    (fun z : ν.1 => P z.val.1) (Real.log (2:ℝ))
  let CB := sourceOriginalCandidateLogCells434
    (fun z : ν.2 => P z.val.1) (Real.log (2:ℝ))
  let idxSource : X → ℤ := fun s =>
    sourceOriginalLiteralLogCellIndex434 (Real.log (2:ℝ))
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (s g i).val))
  let idxTarget : X → ℤ := fun v =>
    sourceOriginalLiteralLogCellIndex434 (Real.log (2:ℝ))
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (v g i).val))
  have hCB (s : X) : idxSource s ∈ CB :=
    source_original_probe_true_source_dyad_covered434
      J ell m hmJ ν P s
  have hCA (v : X) : idxTarget v ∈ CA :=
    source_original_probe_true_target_dyad_covered434
      J ell m hmJ ν P v
  change (∑ ij ∈ CB.product CA,
       ∑ ab : X × X,
         if idxSource ab.1 = ij.1 ∧ idxTarget ab.2 = ij.2
         then z ab else 0) = ∑ ab : X × X, z ab
  exact source_original_finite_two_ended_dyad_partition434
    CB CA idxSource idxTarget hCB hCA z
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeTruePhysicalGlobalCellPartition -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13500000

/-- The TRUE SOURCE03 physical free SOURCE state's originally
selected B-product belongs to an ACTUALLY ATTAINABLE global
cell for the requested literal width hB. This is for every
arbitrary full ordered prime-mark state, not only selected
B-tuples or the log(2) dyadic approximation. -/
theorem source_original_probe_true_source_GLOBAL_cell_covered434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (hB : ℝ)
    (s : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ P g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) :
    sourceOriginalLiteralLogCellIndex434 hB
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (s g i).val)) ∈
    sourceOriginalCandidateLogCells434
      (fun z : ν.2 => P z.val.1) hB := by
  classical
  let e := sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν
  let f : ν.2 → ℕ := fun z => (s (e z).1 (e z).2).val
  have hf : f ∈ Fintype.piFinset
      (fun z : ν.2 => P z.val.1) := by
    apply Fintype.mem_piFinset.mpr
    intro z
    exact (s (e z).1 (e z).2).property
  have hp :
      sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (s g i).val) = ∏ z : ν.2, f z := by
    rfl
  unfold sourceOriginalCandidateLogCells434
  exact Finset.mem_image.mpr ⟨f,hf,by rw [hp]⟩

/-- The TRUE SOURCE03 physical free TARGET state's selected
A-product has its genuine original global cell at the
requested source hA width. Other target marks are retained. -/
theorem source_original_probe_true_target_GLOBAL_cell_covered434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (hA : ℝ)
    (v : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ P g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) :
    sourceOriginalLiteralLogCellIndex434 hA
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (v g i).val)) ∈
    sourceOriginalCandidateLogCells434
      (fun z : ν.1 => P z.val.1) hA := by
  classical
  let e := sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν
  let f : ν.1 → ℕ := fun z => (v (e z).1 (e z).2).val
  have hf : f ∈ Fintype.piFinset
      (fun z : ν.1 => P z.val.1) := by
    apply Fintype.mem_piFinset.mpr
    intro z
    exact (v (e z).1 (e z).2).property
  have hp :
      sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (v g i).val) = ∏ z : ν.1, f z := by
    rfl
  unfold sourceOriginalCandidateLogCells434
  exact Finset.mem_image.mpr ⟨f,hf,by rw [hp]⟩

/-- EXACT partition of every SOURCE03 full physical free-mark
bilinear sum by its own, truly attainable SOURCE-B/TARGET-A
GLOBAL cell pair, with widths hB and hA (not log 2).
No factorization, product-atom replacement, averaging loss,
or phase/sign assumption on the arbitrary joint kernel H. -/
theorem source_original_probe_true_physical_GLOBAL_cell_partition434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (hA hB : ℝ)
    (H : (SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ P g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) ×
      (SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ P g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) → ℂ) :
    let X := SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ P g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)
    let CB := sourceOriginalCandidateLogCells434
      (fun z : ν.2 => P z.val.1) hB
    let CA := sourceOriginalCandidateLogCells434
      (fun z : ν.1 => P z.val.1) hA
    let idxS : X → ℤ := fun s =>
      sourceOriginalLiteralLogCellIndex434 hB
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
          (fun g i => (s g i).val))
    let idxT : X → ℤ := fun v =>
      sourceOriginalLiteralLogCellIndex434 hA
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
          (fun g i => (v g i).val))
    (∑ ij ∈ CB.product CA, ∑ ab : X × X,
      if idxS ab.1 = ij.1 ∧ idxT ab.2 = ij.2
      then H ab else 0) = ∑ ab : X × X, H ab := by
  classical
  dsimp only
  let X := SourceOriginalVariableBIGState434
    (fun g : G => {p : ℕ // p ∈ P g})
    (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)
  let CB := sourceOriginalCandidateLogCells434
    (fun z : ν.2 => P z.val.1) hB
  let CA := sourceOriginalCandidateLogCells434
    (fun z : ν.1 => P z.val.1) hA
  let idxS : X → ℤ := fun s =>
    sourceOriginalLiteralLogCellIndex434 hB
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (s g i).val))
  let idxT : X → ℤ := fun v =>
    sourceOriginalLiteralLogCellIndex434 hA
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (v g i).val))
  have hCoverS (s : X) : idxS s ∈ CB :=
    source_original_probe_true_source_GLOBAL_cell_covered434
      J ell m hmJ ν P hB s
  have hCoverT (v : X) : idxT v ∈ CA :=
    source_original_probe_true_target_GLOBAL_cell_covered434
      J ell m hmJ ν P hA v
  exact source_original_finite_two_ended_dyad_partition434
    CB CA idxS idxT hCoverS hCoverT H
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeTrueDyadEnergy -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- BOTH ACTUAL SOURCE03 ν-dependent endpoint weighted L²
energies are EXACTLY partitioned by the corresponding TRUE
source B and target A product-dyad index. The selected
prime-product indices are those of the real original physical
free-slot arrays; tests depend on ALL physical group marks.
No product-test independence, uniform prime support, or
cardinality loss enters these exact energy identities. -/
theorem source_original_probe_true_source_target_dyad_energy_partition434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (sourceTest targetTest : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ P g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ) :
    let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let prime : (g : G) → BP g → ℕ := fun g p => p.val
    let mu := sourceOriginalJointHarmonicMu434 BP prime V
    let w := sourceOriginalVariableBIGMass434 BP t mu
    let CB := sourceOriginalCandidateLogCells434
      (fun z : ν.2 => P z.val.1) (Real.log (2:ℝ))
    let CA := sourceOriginalCandidateLogCells434
      (fun z : ν.1 => P z.val.1) (Real.log (2:ℝ))
    let idxS : SourceOriginalVariableBIGState434 BP t → ℤ := fun s =>
      sourceOriginalLiteralLogCellIndex434 (Real.log (2:ℝ))
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
          (fun g i => (s g i).val))
    let idxT : SourceOriginalVariableBIGState434 BP t → ℤ := fun v =>
      sourceOriginalLiteralLogCellIndex434 (Real.log (2:ℝ))
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
          (fun g i => (v g i).val))
    (∑ i ∈ CB,
       ∑ s : SourceOriginalVariableBIGState434 BP t,
         if idxS s = i then w s*‖sourceTest s‖^2 else 0) =
       sourceOriginalVariableBIGEnergy434 BP t mu sourceTest ∧
    (∑ j ∈ CA,
       ∑ v : SourceOriginalVariableBIGState434 BP t,
         if idxT v = j then w v*‖targetTest v‖^2 else 0) =
       sourceOriginalVariableBIGEnergy434 BP t mu targetTest := by
  classical
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : G) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let CB := sourceOriginalCandidateLogCells434
    (fun z : ν.2 => P z.val.1) (Real.log (2:ℝ))
  let CA := sourceOriginalCandidateLogCells434
    (fun z : ν.1 => P z.val.1) (Real.log (2:ℝ))
  let idxS : X → ℤ := fun s =>
    sourceOriginalLiteralLogCellIndex434 (Real.log (2:ℝ))
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (s g i).val))
  let idxT : X → ℤ := fun v =>
    sourceOriginalLiteralLogCellIndex434 (Real.log (2:ℝ))
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (v g i).val))
  have hS (s : X) : idxS s ∈ CB :=
    source_original_probe_true_source_dyad_covered434
      J ell m hmJ ν P s
  have hT (v : X) : idxT v ∈ CA :=
    source_original_probe_true_target_dyad_covered434
      J ell m hmJ ν P v
  have hSsum := source_original_finite_dyad_energy_partition434
    CB idxS hS w sourceTest
  have hTsum := source_original_finite_dyad_energy_partition434
    CA idxT hT w targetTest
  have hEs : (∑ s : X, w s*‖sourceTest s‖^2) =
      sourceOriginalVariableBIGEnergy434 BP t mu sourceTest := by
    unfold sourceOriginalVariableBIGEnergy434
    simp only [Complex.normSq_eq_norm_sq]
    rfl
  have hEt : (∑ v : X, w v*‖targetTest v‖^2) =
      sourceOriginalVariableBIGEnergy434 BP t mu targetTest := by
    unfold sourceOriginalVariableBIGEnergy434
    simp only [Complex.normSq_eq_norm_sq]
    rfl
  constructor
  · change (∑ i ∈ CB,
      ∑ s : X, if idxS s = i
        then w s*‖sourceTest s‖^2 else 0) =
      sourceOriginalVariableBIGEnergy434 BP t mu sourceTest
    exact hSsum.trans hEs
  · change (∑ j ∈ CA,
      ∑ v : X, if idxT v = j
        then w v*‖targetTest v‖^2 else 0) =
      sourceOriginalVariableBIGEnergy434 BP t mu targetTest
    exact hTsum.trans hEt
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSameCellSlowPhase -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The exponential is Lipschitz on any common upper-bounded
range, with the *upper endpoint* exponential as its derivative
bound. This elementary estimate is unconditional. -/
theorem source_original_exp_difference_upper434
    (x y R : ℝ)
    (hx : Real.exp x ≤ R) (hy : Real.exp y ≤ R) :
    |Real.exp x - Real.exp y| ≤ R*|x-y| := by
  by_cases hxy : x ≤ y
  · have hd : 0 ≤ y-x := sub_nonneg.mpr hxy
    have hExp : Real.exp y - Real.exp x ≤
        Real.exp y*(y-x) := by
      have hLower := Real.add_one_le_exp (x-y)
      have hBound : Real.exp y*((x-y)+1) ≤ Real.exp x := by
        calc
          _ ≤ Real.exp y*Real.exp (x-y) :=
            mul_le_mul_of_nonneg_left hLower (Real.exp_pos y).le
          _ = Real.exp x := by
            rw [← Real.exp_add]
            congr 1
            ring
      nlinarith [hBound]
    have hm : Real.exp y*(y-x) ≤ R*(y-x) :=
      mul_le_mul_of_nonneg_right hy hd
    have hl : Real.exp x - Real.exp y ≤ 0 :=
      sub_nonpos.mpr (Real.exp_le_exp.mpr hxy)
    have hl2 : x-y ≤ 0 := sub_nonpos.mpr hxy
    rw [abs_of_nonpos hl,abs_of_nonpos hl2]
    linarith
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hd : 0 ≤ x-y := sub_nonneg.mpr hyx
    have hExp : Real.exp x - Real.exp y ≤
        Real.exp x*(x-y) := by
      have hLower := Real.add_one_le_exp (y-x)
      have hBound : Real.exp x*((y-x)+1) ≤ Real.exp y := by
        calc
          _ ≤ Real.exp x*Real.exp (y-x) :=
            mul_le_mul_of_nonneg_left hLower (Real.exp_pos x).le
          _ = Real.exp y := by
            rw [← Real.exp_add]
            congr 1
            ring
      nlinarith [hBound]
    have hm : Real.exp x*(x-y) ≤ R*(x-y) :=
      mul_le_mul_of_nonneg_right hx hd
    have hl : 0 ≤ Real.exp x - Real.exp y :=
      sub_nonneg.mpr (Real.exp_le_exp.mpr hyx)
    have hl2 : 0 ≤ x-y := hd
    rw [abs_of_nonneg hl,abs_of_nonneg hl2]
    linarith
/-- For positive original natural prime products bounded by R,
their *linear* separation is controlled by R times their LOG
separation; no artificial bound on the number of primes or
extra small parameter is inserted. -/
theorem source_original_prime_products_log_to_linear434
    (D X : ℕ) (R : ℝ)
    (hD : 0 < D) (hX : 0 < X)
    (hDR : (D:ℝ) ≤ R) (hXR : (X:ℝ) ≤ R) :
    |(D:ℝ)-(X:ℝ)| ≤
      R*|Real.log (D:ℝ)-Real.log (X:ℝ)| := by
  have hd : (0:ℝ) < D := by exact_mod_cast hD
  have hx : (0:ℝ) < X := by exact_mod_cast hX
  have hExpD : Real.exp (Real.log (D:ℝ)) ≤ R := by
    simpa only [Real.exp_log hd] using hDR
  have hExpX : Real.exp (Real.log (X:ℝ)) ≤ R := by
    simpa only [Real.exp_log hx] using hXR
  have hbound := source_original_exp_difference_upper434
    (Real.log (D:ℝ)) (Real.log (X:ℝ)) R hExpD hExpX
  simpa only [Real.exp_log hd,Real.exp_log hx] using hbound

/-- Two ORIGINAL positive prime products in the same half-open
GLOBAL source03 log-product cell differ in log by at most the
actual cell mesh width h, not by the number of prime marks. -/
theorem source_original_same_global_log_cell_distance434
    (h : ℝ) (hh : 0 < h) (j : ℤ) (D X : ℕ)
    (hD : sourceOriginalLiteralLogCell434 h j D)
    (hX : sourceOriginalLiteralLogCell434 h j X) :
    |Real.log (D:ℝ)-Real.log (X:ℝ)| ≤ h := by
  have h1 : Real.log (D:ℝ)-Real.log (X:ℝ) ≤ h := by
    unfold sourceOriginalLiteralLogCell434 at hD hX
    nlinarith [hD.2,hX.1]
  have h2 : -(h:ℝ) ≤ Real.log (D:ℝ)-Real.log (X:ℝ) := by
    unfold sourceOriginalLiteralLogCell434 at hD hX
    nlinarith [hX.2,hD.1]
  exact abs_le.mpr ⟨h2,h1⟩

/-- The FULL source03 small irrational additive phase beta and
Mellin oscillation zeta are both controlled, on the original
GLOBAL log-product cell, by exactly the cell mesh h:
  |M(D)-M(X)| ≤ (|zeta|+2*pi*|beta| * R)*h.
D and X are actual positive natural products, bounded by R.
This removes any unproved derivative/mean-value hypothesis
from the MAJOR-ARC slow-multiplier replacement. -/
theorem source_original_same_cell_slow_mellin_perturbation434
    (ζ beta : ℝ) (h : ℝ) (hh : 0 < h) (j : ℤ)
    (D X : ℕ) (R : ℝ)
    (hDpos : 0 < D) (hXpos : 0 < X)
    (hDR : (D:ℝ) ≤ R) (hXR : (X:ℝ) ≤ R)
    (hDcell : sourceOriginalLiteralLogCell434 h j D)
    (hXcell : sourceOriginalLiteralLogCell434 h j X) :
    ‖sourceOriginalSlowMellinAdditivePhase434 ζ beta D -
      sourceOriginalSlowMellinAdditivePhase434 ζ beta X‖ ≤
      (|ζ|+2*Real.pi*|beta| * R)*h := by
  let lD : ℝ := Real.log (D:ℝ)-Real.log (X:ℝ)
  have hLog : |lD| ≤ h :=
    source_original_same_global_log_cell_distance434
      h hh j D X hDcell hXcell
  have hDist : |(D:ℝ)-(X:ℝ)| ≤ R*|lD| :=
    source_original_prime_products_log_to_linear434
      D X R hDpos hXpos hDR hXR
  have hβ : 0 ≤ 2*Real.pi*|beta| := by positivity
  have hR : 0 ≤ R := by
    have hp : (0:ℝ) < D := by exact_mod_cast hDpos
    linarith
  have hCoeff : 0 ≤ |ζ|+2*Real.pi*|beta| * R := by positivity
  calc
    _ ≤ |ζ| * |lD| +
      (2*Real.pi*|beta|) * |(D:ℝ)-(X:ℝ)| :=
      source_original_slow_mellin_additive_phase_oscillation434
        ζ beta D X
    _ ≤ |ζ| * |lD|+(2*Real.pi*|beta|)*(R*|lD|) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hDist hβ)
    _ = (|ζ|+2*Real.pi*|beta| * R)*|lD| := by ring
    _ ≤ (|ζ|+2*Real.pi*|beta| * R)*h :=
      mul_le_mul_of_nonneg_left hLog hCoeff
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSharedGroupCount -/

section

open Filter
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The actual original selected-small + other-small + big group family
satisfies the cardinality gate for dirty physical rows. The selected
small group contributes ONE extra slot-family, not an unstated O(T). -/
theorem eventually_source_original_shared_group_count434
    (C0 : ℝ) (hC0 : 0 ≤ C0) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {ι β : Type} [Fintype ι] [Fintype β],
        (Fintype.card ι:ℝ) ≤ C0*Real.log L →
        (Fintype.card β:ℝ) ≤ C0*Real.log L →
        (Fintype.card (Unit ⊕ (ι ⊕ β)):ℝ) ≤
          (2*C0+1)*Real.log L := by
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with L hL
  have hlog : 1 ≤ Real.log L := by
    have hh := Real.log_le_log (Real.exp_pos 1) hL
    simpa only [Real.log_exp] using hh
  intro ι β _ _ hS hB
  have hCard : (Fintype.card (Unit ⊕ (ι ⊕ β)):ℝ) =
      1+(Fintype.card ι:ℝ)+(Fintype.card β:ℝ) := by
    simp only [Fintype.card_sum, Fintype.card_unit]
    push_cast
    ring
  rw [hCard]
  nlinarith
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSharedGroupDisjoint -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- Exact group disjointness for the source distinguished-small,
other-small, big split. The original C data already supplies the
first two hypotheses; the remaining three are explicitly required
by the source03 group geometry, not silently manufactured. -/
theorem source_original_complete_group_disjoint434
    {ι β : Type} [DecidableEq ι] [DecidableEq β]
    (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (hST : ∀ i p, p ∈ S → p ∉ Ts i)
    (hSB : ∀ j p, p ∈ S → p ∉ Tb j)
    (hTT : ∀ i j p, p ∈ Ts i → p ∈ Ts j → i=j)
    (hBB : ∀ i j p, p ∈ Tb i → p ∈ Tb j → i=j)
    (hTB : ∀ i j p, p ∈ Ts i → p ∉ Tb j) :
    ∀ g h : Unit ⊕ (ι ⊕ β), ∀ p : ℕ,
      p ∈ (Sum.elim (fun _ : Unit => S) (Sum.elim Ts Tb)) g →
      p ∈ (Sum.elim (fun _ : Unit => S) (Sum.elim Ts Tb)) h →
      g=h := by
  intro g h p hg hh
  cases g with
  | inl u =>
    cases u
    cases h with
    | inl v => cases v; rfl
    | inr v =>
      cases v with
      | inl i =>
        exact ((hST i p hg) hh).elim
      | inr j =>
        exact ((hSB j p hg) hh).elim
  | inr g =>
    cases g with
    | inl i =>
      cases h with
      | inl v =>
        cases v
        exact ((hST i p hh) hg).elim
      | inr v =>
        cases v with
        | inl j =>
          exact congrArg (fun z : ι => (Sum.inr (Sum.inl z) : Unit ⊕ (ι ⊕ β)))
            (hTT i j p hg hh)
        | inr j =>
          exact ((hTB i j p hg) hh).elim
    | inr i =>
      cases h with
      | inl v =>
        cases v
        exact ((hSB i p hh) hg).elim
      | inr v =>
        cases v with
        | inl j =>
          exact ((hTB j i p hh) hg).elim
        | inr j =>
          exact congrArg (fun z : β => (Sum.inr (Sum.inr z) : Unit ⊕ (ι ⊕ β)))
            (hBB i j p hg hh)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSource03ActualBigUpper -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The old source03 record ALREADY implies the genuine
upper BIG-prime support p<=exp(sqrt L): every Tb(g)
belongs to the original coarse prime set G, by d.hG.
No new support-bound hypothesis is needed. -/
theorem source_original_source03_true_big_prime_upper434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (g : β) (p : ℕ) (hp : p ∈ d.Tb g) :
    (p:ℝ) ≤ Real.exp (Real.sqrt L) := by
  have hbig : p ∈ (Finset.univ : Finset β).biUnion d.Tb := by
    exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,hp⟩
  have hcoarse : p ∈ d.G := by
    rw [d.hG]
    exact Finset.mem_union.mpr (Or.inr hbig)
  exact d.hGroup p hcoarse

/-- Every two selected BIG blocks obey source03's TRUE
logarithmic group-count budget. This is the original
C0 bound, with m<=tmax, not an unproved new exponent. -/
theorem source_original_source03_two_big_block_card_budget434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (blockA blockB : Finset β) (m : ℕ)
    (hm : m ≤ cfg.tmax) (hL : 1 ≤ L) :
    ((m*(blockA.card+blockB.card):ℕ):ℝ) ≤
      (2*(cfg.tmax:ℝ)*cfg.C0)*Real.log L := by
  have hA : blockA.card ≤ Fintype.card β :=
    Finset.card_le_univ blockA
  have hB : blockB.card ≤ Fintype.card β :=
    Finset.card_le_univ blockB
  have hSum : blockA.card+blockB.card ≤
      2*(Fintype.card β) := by omega
  have hN : m*(blockA.card+blockB.card) ≤
      2*cfg.tmax*(Fintype.card β) := by
    calc
      _ ≤ cfg.tmax*(2*(Fintype.card β)) :=
        Nat.mul_le_mul hm hSum
      _ = 2*cfg.tmax*(Fintype.card β) := by ac_rfl
  have hNr : (((m*(blockA.card+blockB.card):ℕ):ℝ)) ≤
      2*(cfg.tmax:ℝ)*(Fintype.card β:ℝ) := by
    exact_mod_cast hN
  have hCoeff : (0:ℝ) ≤ 2*(cfg.tmax:ℝ) := by positivity
  calc
    _ ≤ 2*(cfg.tmax:ℝ)*(Fintype.card β:ℝ) := hNr
    _ ≤ 2*(cfg.tmax:ℝ)*(cfg.C0*Real.log L) :=
       mul_le_mul_of_nonneg_left d.hBigGroups hCoeff
    _ = (2*(cfg.tmax:ℝ)*cfg.C0)*Real.log L := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSource03GroupSeparation -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The FULL group-geometry hypothesis ACTUALLY stated by
the source03 manuscript: all source groups P_g are pairwise
disjoint. The pre-existing SourceComparisonData434 record
encodes ONLY S versus Ts/Tb disjointness. The additional
two within-family and one cross-family separation clauses
must be supplied explicitly; they are not consequences of
hDisjS/hDisjB.
This structure makes source-paper geometry visible and
prevents the C6 factorial atom bound from silently importing
a false disjointness claim. -/
structure SourceOriginalSource03GroupSeparation434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
       [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι β cfg x L Y Hprime) : Prop where
  hTT : ∀ i j : ι, ∀ p : ℕ,
       p ∈ d.Ts i → p ∈ d.Ts j → i = j
  hBB : ∀ i j : β, ∀ p : ℕ,
       p ∈ d.Tb i → p ∈ d.Tb j → i = j
  hTB : ∀ i : ι, ∀ j : β, ∀ p : ℕ,
       p ∈ d.Ts i → p ∉ d.Tb j

/-- True original source03 group separation delivers exactly
the disjointness statements required by the unconditionally
kernel-proven C6 physical atom bounds, with no need for a
new prime universe and no assumption of groupwise
unique prime values *inside* one group. -/
theorem source_original_source03_group_separation_disjoint434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
       [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d) :
    (∀ i j : ι, i ≠ j → Disjoint (d.Ts i) (d.Ts j)) ∧
    (∀ i j : β, i ≠ j → Disjoint (d.Tb i) (d.Tb j)) ∧
    (∀ i : ι, ∀ j : β, Disjoint (d.Ts i) (d.Tb j)) := by
  constructor
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    exact hij (sep.hTT i j p hpi hpj)
  constructor
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    exact hij (sep.hBB i j p hpi hpj)
  · intro i j
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    exact (sep.hTB i j p hpi) hpj

/-- The entire original S ⊕ Ts ⊕ Tb family inherits
the authentic source03 pairwise disjointness, including
the already recorded S exclusions. The missing support
conditions remain explicit in sep. -/
theorem source_original_source03_all_group_separation434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
       [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d) :
    ∀ g h : Unit ⊕ (ι ⊕ β), ∀ p : ℕ,
      p ∈ (Sum.elim (fun _ : Unit => d.S)
          (Sum.elim d.Ts d.Tb)) g →
      p ∈ (Sum.elim (fun _ : Unit => d.S)
          (Sum.elim d.Ts d.Tb)) h → g=h := by
  exact source_original_complete_group_disjoint434
    d.S d.Ts d.Tb
    (fun i p hp => d.hDisjS i p hp)
    (fun j p hp => d.hDisjB j p hp)
    sep.hTT sep.hBB sep.hTB
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimeHarmonicGreedyBlock -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- An actual nonnegative PRIME-HARMONIC atom pool of enough
total mass admits a nonempty sub-pool with mass in the exact
prescribed interval [v,v+δ). Uses a genuinely MINIMAL finite
subset: no probability heuristic and no additional prime
distribution theorem. The only analytic input is the available
pool mass; later Mertens must supply that input. -/
theorem source_original_finite_harmonic_greedy_block434
    {α : Type} [DecidableEq α]
    (s : Finset α) (w : α → ℝ)
    (v δ : ℝ) (hv : 0 < v)
    (hw : ∀ a ∈ s, 0 ≤ w a ∧ w a ≤ δ)
    (hs : v ≤ ∑ a ∈ s, w a) :
    ∃ t : Finset α,
      t ⊆ s ∧ t.Nonempty ∧
      v ≤ ∑ a ∈ t, w a ∧
      (∑ a ∈ t, w a) < v+δ := by
  classical
  let A : Finset (Finset α) :=
    s.powerset.filter (fun t => v ≤ ∑ a ∈ t, w a)
  have hA : A.Nonempty := by
    refine ⟨s, ?_⟩
    simp [A, hs]
  obtain ⟨t, htA, hmin⟩ :=
    Finset.exists_min_image A (fun t : Finset α => t.card) hA
  have ht : t ⊆ s :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp htA).1
  have htlower : v ≤ ∑ a ∈ t, w a :=
    (Finset.mem_filter.mp htA).2
  have htne : t.Nonempty := by
    by_contra he
    have he0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp [he0] at htlower
    linarith
  refine ⟨t,ht,htne,htlower,?_⟩
  obtain ⟨a,ha⟩ := htne
  have hs_remove : (∑ b ∈ t.erase a, w b) < v := by
    by_contra hn
    have hge : v ≤ ∑ b ∈ t.erase a, w b := le_of_not_gt hn
    have hmem : t.erase a ∈ A := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr
        ((Finset.erase_subset _ _).trans ht), hge⟩
    have hmincard := hmin (t.erase a) hmem
    have hstrict := Finset.card_erase_lt_of_mem ha
    omega
  have hsum := Finset.sum_erase_add t w ha
  have haBound : w a ≤ δ := (hw a (ht ha)).2
  linarith
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPrimeHarmonicFiniteGroups -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- ACTUAL constructive finite-group partition: if a finite
prime harmonic pool carries at least n*(v+δ) reciprocal mass,
and every atom costs <=δ, it contains n PAIRWISE DISJOINT
nonempty groups, EACH of mass [v,v+δ). The groups are
constructed by iterative minimal-cardinality selection.
This is source03 geometry once independent prime-band
lower-mass bounds are supplied. No fictitious independence. -/
theorem source_original_finite_harmonic_disjoint_groups434
    {α : Type} [DecidableEq α]
    (n : ℕ) (s : Finset α) (w : α → ℝ)
    (v δ : ℝ) (hv : 0 < v) (hδ : 0 ≤ δ)
    (hw : ∀ a ∈ s, 0 ≤ w a ∧ w a ≤ δ)
    (hs : (n:ℝ)*(v+δ) ≤ ∑ a ∈ s, w a) :
    ∃ groups : Fin n → Finset α,
      (∀ i, groups i ⊆ s) ∧
      (∀ i, (groups i).Nonempty ∧
        v ≤ ∑ a ∈ groups i, w a ∧
        (∑ a ∈ groups i, w a) < v+δ) ∧
      (∀ i j, i ≠ j → Disjoint (groups i) (groups j)) := by
  classical
  induction n generalizing s with
  | zero =>
      refine ⟨(fun i => Fin.elim0 i), ?_, ?_, ?_⟩
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i
  | succ n ih =>
      have hvplus : 0 ≤ v+δ := add_nonneg hv.le hδ
      have hmu : 0 ≤ (n:ℝ)*(v+δ) :=
        mul_nonneg (Nat.cast_nonneg _) hvplus
      have hsfirst : v ≤ ∑ a ∈ s, w a := by
        push_cast at hs
        nlinarith
      obtain ⟨t, ht, htnonempty, htlow, hthigh⟩ :=
        source_original_finite_harmonic_greedy_block434 s w v δ hv hw hsfirst
      let rem := s \ t
      have hwrem : ∀ a ∈ rem, 0 ≤ w a ∧ w a ≤ δ := by
        intro a ha
        exact hw a (Finset.sdiff_subset ha)
      have hr : (n:ℝ)*(v+δ) ≤ ∑ a ∈ rem, w a := by
        have he := Finset.sum_sdiff_eq_sub ht (f := w)
        dsimp [rem]
        rw [he]
        push_cast at hs
        nlinarith
      obtain ⟨tail, hsub, hmass, hdisj⟩ :=
        ih rem hwrem hr
      let groups : Fin (n+1) → Finset α := Fin.cons t tail
      refine ⟨groups, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [groups,Fin.cons_zero] using ht
        · simpa only [groups,Fin.cons_succ] using
            (hsub j).trans Finset.sdiff_subset
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [groups,Fin.cons_zero] using
            (show t.Nonempty ∧ v ≤ ∑ a ∈ t, w a ∧
              (∑ a ∈ t, w a) < v+δ from ⟨htnonempty,htlow,hthigh⟩)
        · simpa only [groups,Fin.cons_succ] using hmass j
      · intro i j hij
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero => exact (hij rfl).elim
            | succ j =>
                have hd : Disjoint t (tail j) :=
                  Finset.disjoint_of_subset_right (hsub j) Finset.disjoint_sdiff
                simpa only [groups,Fin.cons_zero,Fin.cons_succ] using hd
        | succ i =>
            cases j using Fin.cases with
            | zero =>
                have hd : Disjoint (tail i) t :=
                  (Finset.disjoint_of_subset_right (hsub i)
                    Finset.disjoint_sdiff).symm
                simpa only [groups,Fin.cons_zero,Fin.cons_succ] using hd
            | succ j =>
                have hi : i ≠ j := fun he => hij (congrArg Fin.succ he)
                simpa only [groups,Fin.cons_succ] using hdisj i j hi
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalAbstractFullIntervals -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 100000

/-- Abstract FULL consecutive interval constructor. Unlike a
collection of arbitrary subsets of primes, the intervals have
genuine ordered endpoints. Only a proven additive mass law and
a proven first-threshold prefix lemma are used. This isolates
all dependent Fin-index bookkeeping from the physical arithmetic. -/
theorem source_original_abstract_ordered_full_interval_chain434
    (mass : ℕ → ℕ → ℝ) (base : ℕ)
    (target δ : ℝ) (htarget : 0 < target) (hδ : 0 ≤ δ)
    (hadd : ∀ a b c, a ≤ b → b ≤ c →
        mass a c = mass a b + mass b c)
    (hprefix : ∀ a b, base ≤ a → a ≤ b →
        target ≤ mass a b →
        ∃ m : ℕ, a < m ∧ m ≤ b ∧
          target ≤ mass a m ∧ mass a m < target+δ)
    (n u v : ℕ) (hbu : base ≤ u) (huv : u ≤ v)
    (hlarge : (n:ℝ)*(target+δ) ≤ mass u v) :
    ∃ (left right : Fin n → ℕ),
      (∀ i, u ≤ left i ∧ left i < right i ∧ right i ≤ v) ∧
      (∀ i, target ≤ mass (left i) (right i) ∧
        mass (left i) (right i) < target+δ) ∧
      (∀ i j, i<j → right i ≤ left j) := by
  classical
  induction n generalizing u v with
  | zero =>
      refine ⟨(fun i => Fin.elim0 i),(fun i => Fin.elim0 i),
        ?_,?_,?_⟩
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i
  | succ n ih =>
      have hplus : 0 ≤ target+δ := add_nonneg htarget.le hδ
      have hstep : ((n+1:ℕ):ℝ)*(target+δ) =
          (n:ℝ)*(target+δ)+(target+δ) := by
        push_cast
        ring
      have hsfirst : target ≤ mass u v := by
        rw [hstep] at hlarge
        have hn : 0 ≤ (n:ℝ)*(target+δ) :=
          mul_nonneg (Nat.cast_nonneg _) hplus
        linarith
      obtain ⟨m,hum,hmv,hmass,hshort⟩ :=
        hprefix u v hbu huv hsfirst
      have hrem : (n:ℝ)*(target+δ) ≤ mass m v := by
        have hs := hadd u m v hum.le hmv
        rw [hstep,hs] at hlarge
        linarith
      obtain ⟨leftTail,rightTail,hTRange,hTMass,hTOrdered⟩ :=
        ih m v (hbu.trans hum.le) hmv hrem
      let left : Fin (n+1) → ℕ := Fin.cons u leftTail
      let right : Fin (n+1) → ℕ := Fin.cons m rightTail
      refine ⟨left,right,?_,?_,?_⟩
      · intro i
        cases i using Fin.cases with
        | zero => simpa only [left,right,Fin.cons_zero] using
            (show u ≤ u ∧ u < m ∧ m ≤ v from ⟨le_rfl,hum,hmv⟩)
        | succ i =>
            have hh := hTRange i
            simpa only [left,right,Fin.cons_succ] using
              (show u ≤ leftTail i ∧
                leftTail i < rightTail i ∧ rightTail i ≤ v
                from ⟨hum.le.trans hh.1,hh.2⟩)
      · intro i
        cases i using Fin.cases with
        | zero => simpa only [left,right,Fin.cons_zero] using
            (show target ≤ mass u m ∧ mass u m < target+δ
              from ⟨hmass,hshort⟩)
        | succ i => simpa only [left,right,Fin.cons_succ] using hTMass i
      · intro i j hij
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero => exact (False.elim (lt_irrefl _ hij))
            | succ j =>
                have hh := (hTRange j).1
                simpa only [left,right,Fin.cons_zero,Fin.cons_succ]
                  using hh
        | succ i =>
            cases j using Fin.cases with
            | zero =>
                have hh : i.val + 1 < 0 := by
                  simpa only [Fin.lt_def,Fin.val_succ,Fin.val_zero] using hij
                exact False.elim ((Nat.not_lt_zero _) hh)
            | succ j =>
                have hh : i<j := by
                  exact Fin.succ_lt_succ_iff.mp hij
                simpa only [left,right,Fin.cons_succ] using
                  hTOrdered i j hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03CrossScaleSeparation -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- TRUE original SOURCE03 small and BIG support intervals
cannot share a prime when L>1 and the original fixed
exponents obey b<c. Does NOT assume synthetic numerical
cross-disjointness: the gap exp(L^b)<exp(L^c) proves it
directly. SourceComparisonData does not supply these two
Ts/Tb support inequalities, so they remain EXPLICIT source
construction obligations rather than inferred from d.hSmall. -/
theorem source_original_source03_cross_small_big_gap434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434)
    (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (hL : 1 < L)
    (hTsUpper : ∀ i : ι, ∀ p ∈ d.Ts i,
       (p:ℝ) ≤ Real.exp (L^cfg.bexp))
    (hTbLower : ∀ j : β, ∀ p ∈ d.Tb j,
       Real.exp (L^cfg.cexp) ≤ (p:ℝ)) :
    ∀ i : ι, ∀ j : β, ∀ p ∈ d.Ts i, p ∉ d.Tb j := by
  have hbc : cfg.bexp < cfg.cexp := cfg.hbc
  have hPow : L^cfg.bexp < L^cfg.cexp :=
    Real.rpow_lt_rpow_of_exponent_lt hL hbc
  have hGap : Real.exp (L^cfg.bexp) <
      Real.exp (L^cfg.cexp) :=
    Real.exp_lt_exp.mpr hPow
  intro i j p hp
  intro hpB
  have hLo := hTbLower j p hpB
  have hHi := hTsUpper i p hp
  exact (not_le_of_gt hGap) (hLo.trans hHi)

/-- SOURCE03 true pairwise group separation follows from the
two genuine within-family separations plus the ORIGINAL
small/large logarithmic prime-scale gap. There is NO new
cross-family disjointness hypothesis and no assumption on
marks or analytic tests. This removes hTB as a separate
mathematical obligation once the two source supports are
verified. -/
theorem source_original_source03_separation_from_scales434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434)
    (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (hL : 1 < L)
    (hTsUpper : ∀ i : ι, ∀ p ∈ d.Ts i,
       (p:ℝ) ≤ Real.exp (L^cfg.bexp))
    (hTbLower : ∀ j : β, ∀ p ∈ d.Tb j,
       Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hSmallDisjoint : ∀ i j : ι, ∀ p : ℕ,
       p ∈ d.Ts i → p ∈ d.Ts j → i=j)
    (hBigDisjoint : ∀ i j : β, ∀ p : ℕ,
       p ∈ d.Tb i → p ∈ d.Tb j → i=j) :
    SourceOriginalSource03GroupSeparation434 d := by
  exact {
    hTT := hSmallDisjoint
    hBB := hBigDisjoint
    hTB := source_original_source03_cross_small_big_gap434
      cfg x L Y Hprime d hL hTsUpper hTbLower
  }
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueBigCandidateCells -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- In the original SOURCE03 physical BIG prime regime,
every supported prime satisfies 2 <= p <= exp(L^d).
Thus the NUMBER of genuine log-product cells is at most
ceil(m*L^d/h)+1, where m is the exact number of labelled
prime slots and h is the true global log-cell mesh.
No assumption on which products are active, no fake
product support, and no prime-count factor appears. -/
theorem source_original_true_BIG_candidate_cell_card434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (L d h : ℝ)
    (hL : 1 ≤ L) (hh : 0 < h)
    (hPrime : ∀ i p, p ∈ S i →
        p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d)) :
    (sourceOriginalCandidateLogCells434 S h).card ≤
      Nat.ceil (((Fintype.card ι:ℝ)*L^d)/h)+1 := by
  have hLnonneg : 0 ≤ L := by linarith
  have hBunit : (1:ℝ) ≤ Real.exp (L^d) := by
    have hpower : 0 ≤ L^d := Real.rpow_nonneg hLnonneg _
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hpower)
  have hMin (i : ι) (p : ℕ) (hp : p ∈ S i) : 1 ≤ p := by
    have hPrime' := (hPrime i p hp).1
    exact Nat.succ_le_of_lt hPrime'.pos
  have hMax (i : ι) (p : ℕ) (hp : p ∈ S i) :
      (p:ℝ) ≤ Real.exp (L^d) := (hPrime i p hp).2
  simpa only [Real.log_exp] using
    (source_original_candidate_log_cells_card_by_prime_support434
      S h (Real.exp (L^d)) hh hBunit hMin hMax)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueBigCandidateCellsRealBound -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Real-valued quantitative count of ACTUAL original source03
candidate GLOBAL cells, no ceil or hidden candidate-cardinality
assumption. For arbitrary finite labelled prime support
S_i subset [2,exp(L^d)] and true cell width h>0:
 #candidate cells < m*L^d/h + 2,
m the exact number of labelled prime slots. This is the
precise loss for discarded-cell mass in C134/C144. -/
theorem source_original_true_BIG_candidate_cell_real_bound434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (L d h : ℝ)
    (hL : 1 ≤ L) (hh : 0 < h)
    (hPrime : ∀ i p, p ∈ S i →
        p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d)) :
    ((sourceOriginalCandidateLogCells434 S h).card:ℝ) ≤
      ((Fintype.card ι:ℝ)*L^d)/h+2 := by
  let x : ℝ := ((Fintype.card ι:ℝ)*L^d)/h
  have hx : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ L) _))
      hh.le
  have hcount := source_original_true_BIG_candidate_cell_card434
    S L d h hL hh hPrime
  have hCast :
      ((sourceOriginalCandidateLogCells434 S h).card:ℝ) ≤
        ((Nat.ceil x+1:ℕ):ℝ) := by
    exact_mod_cast hcount
  have hCeil : (Nat.ceil x:ℝ) < x+1 :=
    Nat.ceil_lt_add_one hx
  dsimp [x] at hCast hCeil ⊢
  push_cast at hCast
  linarith
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueCellTwoDyadMask -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Exact original source03 half-open global cell gate equals
the sum of TWO disjoint physical dyad gates, with no loss of
any prime-label-dependent endpoint coefficient. The product
is positive, as it is for each actual supported prime tuple. -/
theorem source_original_true_cell_two_dyad_mask_split434
    (h : ℝ) (hh : h ≤ 1) (j : ℤ)
    (n : ℕ) (hn : 0 < n) (c : ℂ) :
    let M : ℕ := Nat.ceil (Real.exp ((j:ℝ)*h))
    (if sourceOriginalLiteralLogCell434 h j n then c else 0) =
      (if sourceOriginalLiteralLogCell434 h j n ∧
          n ∈ Finset.Ico M (2*M) then c else 0) +
      (if sourceOriginalLiteralLogCell434 h j n ∧
          n ∈ Finset.Ico (2*M) (4*M) then c else 0) := by
  dsimp
  by_cases hc : sourceOriginalLiteralLogCell434 h j n
  · obtain ⟨_,hPart⟩ :=
      source_original_actual_cell_two_dyad_partition434
        h hh j n hn hc
    rcases hPart with hLeft | hRight
    · have hNotRight :
          n ∉ Finset.Ico
            (2*Nat.ceil (Real.exp ((j:ℝ)*h)))
            (4*Nat.ceil (Real.exp ((j:ℝ)*h))) := by
        intro hBoth
        simp only [Finset.mem_Ico] at hLeft hBoth
        omega
      simp [hc,hLeft,hNotRight]
    · have hNotLeft :
          n ∉ Finset.Ico
            (Nat.ceil (Real.exp ((j:ℝ)*h)))
            (2*Nat.ceil (Real.exp ((j:ℝ)*h))) := by
        intro hBoth
        simp only [Finset.mem_Ico] at hRight hBoth
        omega
      simp [hc,hRight,hNotLeft]
  · simp [hc]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueCellFourRectangles -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- A full two-GLOBAL-cell physical bilinear expectation splits
EXACTLY into four integer dyadic rectangles. Supports, weights,
both arbitrary marked endpoint tests and an arbitrarily coupled
signed Fourier/primitive kernel H are unchanged. There is no
assumed bilinear cancellation here: it is an exact geometry and
Fubini bridge enabling four independent C6 applications. -/
theorem source_original_true_two_cell_four_physical_rectangles434
    {X Y : Type} [Fintype X] [Fintype Y]
    (pA : X → ℕ) (pB : Y → ℕ)
    (hPrimeA : ∀ x, 0 < pA x)
    (hPrimeB : ∀ y, 0 < pB y)
    (hA hB : ℝ) (hwA : hA ≤ 1) (hwB : hB ≤ 1)
    (jA jB : ℤ)
    (wA : X → ℂ) (wB : Y → ℂ)
    (fA : X → ℂ) (fB : Y → ℂ)
    (H : X × Y → ℂ) :
    let MA : ℕ := Nat.ceil (Real.exp ((jA:ℝ)*hA))
    let MB : ℕ := Nat.ceil (Real.exp ((jB:ℝ)*hB))
    let a0 : X → ℂ := fun x =>
      if sourceOriginalLiteralLogCell434 hA jA (pA x) ∧
        pA x ∈ Finset.Ico MA (2*MA) then fA x else 0
    let a1 : X → ℂ := fun x =>
      if sourceOriginalLiteralLogCell434 hA jA (pA x) ∧
        pA x ∈ Finset.Ico (2*MA) (4*MA) then fA x else 0
    let b0 : Y → ℂ := fun y =>
      if sourceOriginalLiteralLogCell434 hB jB (pB y) ∧
        pB y ∈ Finset.Ico MB (2*MB) then fB y else 0
    let b1 : Y → ℂ := fun y =>
      if sourceOriginalLiteralLogCell434 hB jB (pB y) ∧
        pB y ∈ Finset.Ico (2*MB) (4*MB) then fB y else 0
    sourceOriginalFiniteTwoSidedMinorBilinear434 wA wB
      (fun x => if sourceOriginalLiteralLogCell434 hA jA (pA x)
        then fA x else 0)
      (fun y => if sourceOriginalLiteralLogCell434 hB jB (pB y)
        then fB y else 0) H =
      sourceOriginalFiniteTwoSidedMinorBilinear434 wA wB a0 b0 H +
      sourceOriginalFiniteTwoSidedMinorBilinear434 wA wB a0 b1 H +
      sourceOriginalFiniteTwoSidedMinorBilinear434 wA wB a1 b0 H +
      sourceOriginalFiniteTwoSidedMinorBilinear434 wA wB a1 b1 H := by
  classical
  let MA : ℕ := Nat.ceil (Real.exp ((jA:ℝ)*hA))
  let MB : ℕ := Nat.ceil (Real.exp ((jB:ℝ)*hB))
  let a0 : X → ℂ := fun x => if
      sourceOriginalLiteralLogCell434 hA jA (pA x) ∧
      pA x ∈ Finset.Ico MA (2*MA) then fA x else 0
  let a1 : X → ℂ := fun x => if
      sourceOriginalLiteralLogCell434 hA jA (pA x) ∧
      pA x ∈ Finset.Ico (2*MA) (4*MA) then fA x else 0
  let b0 : Y → ℂ := fun y => if
      sourceOriginalLiteralLogCell434 hB jB (pB y) ∧
      pB y ∈ Finset.Ico MB (2*MB) then fB y else 0
  let b1 : Y → ℂ := fun y => if
      sourceOriginalLiteralLogCell434 hB jB (pB y) ∧
      pB y ∈ Finset.Ico (2*MB) (4*MB) then fB y else 0
  have hSplitA (x : X) :
      (if sourceOriginalLiteralLogCell434 hA jA (pA x)
        then fA x else 0) = a0 x + a1 x := by
    simpa only [a0,a1,MA] using
      source_original_true_cell_two_dyad_mask_split434
        hA hwA jA (pA x) (hPrimeA x) (fA x)
  have hSplitB (y : Y) :
      (if sourceOriginalLiteralLogCell434 hB jB (pB y)
        then fB y else 0) = b0 y + b1 y := by
    simpa only [b0,b1,MB] using
      source_original_true_cell_two_dyad_mask_split434
        hB hwB jB (pB y) (hPrimeB y) (fB y)
  change
    sourceOriginalFiniteTwoSidedMinorBilinear434 wA wB
      (fun x => if sourceOriginalLiteralLogCell434 hA jA (pA x)
        then fA x else 0)
      (fun y => if sourceOriginalLiteralLogCell434 hB jB (pB y)
        then fB y else 0) H =
    sourceOriginalFiniteTwoSidedMinorBilinear434 wA wB a0 b0 H +
    sourceOriginalFiniteTwoSidedMinorBilinear434 wA wB a0 b1 H +
    sourceOriginalFiniteTwoSidedMinorBilinear434 wA wB a1 b0 H +
    sourceOriginalFiniteTwoSidedMinorBilinear434 wA wB a1 b1 H
  unfold sourceOriginalFiniteTwoSidedMinorBilinear434
  calc
    _ = ∑ q : X × Y,
       (wA q.1*wB q.2*a0 q.1*b0 q.2*H q +
        wA q.1*wB q.2*a0 q.1*b1 q.2*H q +
        wA q.1*wB q.2*a1 q.1*b0 q.2*H q +
        wA q.1*wB q.2*a1 q.1*b1 q.2*H q) := by
          apply Finset.sum_congr rfl
          intro q hq
          dsimp only
          rw [hSplitA q.1,hSplitB q.2]
          ring
    _ = _ := by simp only [Finset.sum_add_distrib]
end Green64Analytic.CorrelationSquare

end

