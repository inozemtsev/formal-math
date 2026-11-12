module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Reflection.Part007
public import Green64.Library.Analysis.NumberTheory.DirichletL.Reflection.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Reflection.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Reflection.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.Reflection.Part006
public import Green64.Library.Analysis.NumberTheory.DirichletL.Reflection.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part002

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Reflection / Part008

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Reflection.OriginalRetained -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_sector_retained_energy
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤ margin → d≤ cstar/200 →
      η≤ cstar/1000 → δ+η≤ cstar/1000 → π≤ cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ),
        literalDyadicRow G K.val (hrows K.val K.property) S j Pset
          (E.completion K) s hc₀ u i W θ X r aw‖^2)≤
        C*((retainedDyads (familyRawScale G s X QK QP) (16*Z^δ)).card:ℝ)^2*(1+‖θ‖)^degree*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(F₀-cstar/4-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_sector_literal_energy
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
  refine ⟨degree,36*C,Z₀,by positivity,hZ₀,?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let : Finite Eisˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Eisˣ := Fintype.ofFinite _
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let Dset := retainedDyads (familyRawScale G s X QK QP) (16*Z^δ)
  let src := fun (ui : Eisˣ×(ℕ×ℕ×ℕ)) (K : rows) =>
    literalDyadicRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ ui.1 ui.2 W θ X r aw
  have hb (ui : Eisˣ×(ℕ×ℕ×ℕ)) (hui : ui∈(Finset.univ:Finset Eisˣ)×ˢDset) :=
    henergy J I F B R Q₀ hJ hI hF hB hR hpower hmask A
      Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot ui.2
      hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
      heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hscap
      (Finset.mem_product.mp hui).2 rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar
      ui.1 θ r aw hqk hqp hKr hPr hr haw
  have hh := weighted_finite_row_energy_uniform ((Finset.univ:Finset Eisˣ)×ˢDset) (Finset.univ:Finset rows)
    (fun _ => (1:ℂ)) src _ hb
  have hcard : Fintype.card Eisˣ=6 := by
    rw [←Nat.card_eq_fintype_card]
    exact PrimaryIdealUnitReindex.card_units_eq_six
  simp only [src,one_mul,norm_one,Finset.sum_const,nsmul_eq_mul,mul_one,
    Finset.card_product,Finset.card_univ,hcard,Finset.sum_product,tsum_fintype] at hh ⊢
  apply hh.trans_eq
  push_cast
  ring
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.RetainedBudget -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_sector_retained_budget
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (_hLpool : 0≤Lpool) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤ margin → d≤ cstar/200 →
      η≤ cstar/1000 → δ+η≤ cstar/1000 → π≤ cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool → κ+ρ*Lpool≤ cstar/16 →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ),
        literalDyadicRow G K.val (hrows K.val K.property) S j Pset
          (E.completion K) s hc₀ u i W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_sector_retained_energy
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
  obtain ⟨Cd,hCd,hcount⟩ := retained_count_budget κ δ Lscale hκ hδL
  refine ⟨degree,C*Cd,Z₀,mul_pos hC hCd,hZ₀,?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hpool hsmall rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  have hz' : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hzpos : 0<Z := lt_trans zero_lt_one hz'
  have hs := henergy J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hscap
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  have hd := hcount Z (familyRawScale G s X QK QP) hz'.le hscap
  have hp : (Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ≤Z^(Lpool*ρ) := by
    rw [Real.rpow_mul hzpos.le]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hpool hρ.le
  apply hs.trans
  calc
    _ ≤ C*(Cd*Z^κ)*(1+‖θ‖)^degree*Z^(Lpool*ρ)*Z^(F₀-cstar/4-O₀/2) := by gcongr
    _ = (C*Cd)*(1+‖θ‖)^degree*Z^(κ+Lpool*ρ+(F₀-cstar/4-O₀/2)) := by
      rw [Real.rpow_add hzpos,Real.rpow_add hzpos]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hz'.le (by nlinarith only [hsmall])) (by positivity)
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.UniformNormalizedUniformDegree -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
universe u v

theorem normalized_surviving_physical_source_energy_type_uniform_uniform_degree
    (ε : ℝ) (hε : 0<ε) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) (hM : ∀ i, 0≤M i)
    (hwindowNorm : ∀ i y, ‖windows i y‖≤1)
    (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (kK kP kn kb η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hkn : 0<kn) (hkb : 0<kb) (hη : 0<η) :
    ∃ (degree : ℕ), ∀ {N a c : Eis} {mode : Bool}
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
    ∃ (C₀ C Z₀ : ℝ), 0≤C₀ ∧ 0<C ∧ 1<Z₀ ∧
    ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ Z : ℝ, Z₀≤Z →
    ∀ (X Y B L : ℝ), 1≤X → 1≤Y → 1≤B → 1≤L →
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ),
      (9:Eis)*c ∣ N → (if mode then λ₀^2∣a-1 else λ₀^2∣c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis⧸F.ideal f)≠2) → (∀ f, jF f<6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (T θ QK QP Qn Qb : ℝ),
      0<T → 0<QK → 0<QP → 0<Qn → 0<Qb →
      X=kK*QK → Y=kn*Qn → B=kb*Qb → L=kP*QP →
    ∀ (rows nset bset Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ)≤X)
      (D : ∀ K : rows, ∀ P : Pset, IsCoprime K.val P.val →
        ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property).1 (S P.val)).generator N a c mode)
      (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ),
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis⧸(F.sum (S P)).ideal i)≠2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ)≤Y) →
      (∀ b ∈ bset, primaryGenerator b≠0 ∧ (Ideal.absNorm b:ℝ)≤B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤2*L) →
      (∀ K P hp, (D K P hp).fixedFactor=D0.fixedFactor) →
      (∀ K P hp u m n b, actualCuspColumn (D K P hp) s hc u m n b=actualCuspColumn D0 s hc u m n b) →
      (∀ K ∈ rows, ‖r₀ K‖≤1) → (∀ P ∈ Pset, ‖aw₀ P‖≤1) → (∀ n b, ‖w₀ n b‖≤1) →
      let branches := survivingFrozenBranches F jF (actualCuspColumn D0 s hc u m) nset bset
      (∑ K : rows, ‖weightedFinitePhysicalKernelRow F K.val (hrows K.val K.property).1 S jF Pset nset bset
        (D K) s hc u m windows QK QP Qn Qb W θ T r₀ aw₀ w₀‖^2) ≤
      ((branches.card:ℝ)*∑ e∈branches,
        let U := Y/Ideal.absNorm (frozenExtracted F jF e 1)
        let Bb := B/Ideal.absNorm (frozenExtracted F jF e 2)
        (Real.exp (M 2/2+M 3)*Real.sqrt kn*kb)^2*(6*C)*Z^(
          InverseTerminalWidths.reflectedExponent 0 (Real.logb Z X)
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
            (Real.logb Z L) (Real.logb Z U) (Real.logb Z Bb)
            (InverseTerminalWidths.ramifiedWidth Z m)
            (InverseTerminalWidths.terminalDualWidth Z (Real.logb Z X) (Real.logb Z L) (Real.logb Z T) F.ideal jF e)+
          ε*(Real.logb Z X+Real.logb Z U+Real.logb Z Bb+Real.logb Z L)+η/2))*(C₀*(1+‖θ‖)^degree)^2 := by
  obtain ⟨degree,huniform⟩ := surviving_physical_source_energy_type_uniform_uniform_degree
    ε hε a₀ b₀ ha₀ windows M hM hwindowNorm hwindows W hWsupport hW
  refine ⟨degree,?_⟩
  intro N a c mode s hc
  obtain ⟨C₀,C,hC₀,hC,hsource⟩ := huniform (N:=N) (a:=a) (c:=c) (mode:=mode)
  obtain ⟨Z₀,hZ₀,hshape⟩ := actual_physical_shape_uniform_type_uniform s hc
    kK kP kn kb η hkK hkP hkn hkb hη
  refine ⟨C₀,C,Z₀,hC₀,hC,hZ₀,?_⟩
  intro φ σ _ _ Z hZ X Y B L hX hY hB hL F jF hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m T θ QK QP Qn Qb hT hQK hQP hQn hQb hsX hsY hsB hsL
    rows nset bset Pset S hrows D r₀ aw₀ w₀
    hrowcop hproducts hScop hSN hSchar hn hb hP hκ hA hr₀ haw₀ hw₀
  have hh := hsource X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    G0 D0 u m T θ QK QP Qn Qb hT hQK hQP hQn hQb rows nset bset Pset S hrows D r₀ aw₀ w₀
    hrowcop hproducts hScop hSN hSchar hn hb hP hκ hA hr₀ haw₀ hw₀
  let branches := survivingFrozenBranches F jF (actualCuspColumn D0 s hc u m) nset bset
  let scalar := Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*
    smallScalar (kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb)
  dsimp only at hh ⊢
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  rw [mul_left_comm (scalar^2) (branches.card:ℝ)]
  rw [Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro e he
  obtain ⟨heY,heB⟩ := surviving_extracted_scales F hF jF (actualCuspColumn D0 s hc u m)
    nset bset Y B (fun n h => ⟨(hn n h).1.2,(hn n h).2⟩) hb e he
  rw [heY,heB]
  have hee := hshape Z hZ F jF e m T QK QP Qn Qb (Real.exp (M 2/2+M 3)) C ε hT hQK hQP hQn hQb hC.le
  dsimp only at hee
  rw [hsX,hsY,hsB,hsL]
  convert hee using 1 ; ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.SectorNormalizedUniformDegree -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
universe u v

theorem sector_normalized_physical_energy_uniform_degree
    (ε : ℝ) (hε : 0<ε) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) (hM : ∀ i, 0≤M i)
    (hwindowNorm : ∀ i y, ‖windows i y‖≤1)
    (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (kK kP kn kb η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hkn : 0<kn) (hkb : 0<kb) (hη : 0<η) :
    ∃ (degree : ℕ), ∀ {N a c : Eis} {mode : Bool}
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
    ∃ (C₀ C Z₀ : ℝ), 0≤C₀ ∧ 0<C ∧ 1<Z₀ ∧
    ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ Z : ℝ, Z₀≤Z →
    ∀ (X Y B L : ℝ), 1≤X → 1≤Y → 1≤B → 1≤L →
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ),
      (9:Eis)*c ∣ N → (if mode then λ₀^2∣a-1 else λ₀^2∣c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis⧸F.ideal f)≠2) → (∀ f, jF f<6) →
    ∀ (u : Eisˣ) (m : ℕ) (T θ QK QP Qn Qb : ℝ),
      0<T → 0<QK → 0<QP → 0<Qn → 0<Qb →
      X=kK*QK → Y=kn*Qn → B=kb*Qb → L=kP*QP →
    ∀ (rows nset bset Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ)≤X)
      (E : SectorArithmetic (N:=N) F rows Pset S (fun K hK => (hrows K hK).1) s hc)
      (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ),
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis⧸(F.sum (S P)).ideal i)≠2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ)≤Y) →
      (∀ b ∈ bset, primaryGenerator b≠0 ∧ (Ideal.absNorm b:ℝ)≤B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤2*L) →
      (∀ K ∈ rows, ‖r₀ K‖≤1) → (∀ P ∈ Pset, ‖aw₀ P‖≤1) → (∀ n b, ‖w₀ n b‖≤1) →
      let branches := survivingFrozenBranches F jF (actualCuspColumn E.referenceArithmetic s hc u m) nset bset
      (∑ K : rows, ‖weightedFinitePhysicalKernelRow F K.val (hrows K.val K.property).1 S jF Pset nset bset
        (E.completion K) s hc u m windows QK QP Qn Qb W θ T r₀ aw₀ w₀‖^2) ≤
      ((branches.card:ℝ)*∑ e∈branches,
        let U := Y/Ideal.absNorm (frozenExtracted F jF e 1)
        let Bb := B/Ideal.absNorm (frozenExtracted F jF e 2)
        (Real.exp (M 2/2+M 3)*Real.sqrt kn*kb)^2*(6*C)*Z^(
          InverseTerminalWidths.reflectedExponent 0 (Real.logb Z X)
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
            (Real.logb Z L) (Real.logb Z U) (Real.logb Z Bb)
            (InverseTerminalWidths.ramifiedWidth Z m)
            (InverseTerminalWidths.terminalDualWidth Z (Real.logb Z X) (Real.logb Z L) (Real.logb Z T) F.ideal jF e)+
          ε*(Real.logb Z X+Real.logb Z U+Real.logb Z Bb+Real.logb Z L)+η/2))*(C₀*(1+‖θ‖)^degree)^2 := by
  obtain ⟨degree,huniform⟩ := normalized_surviving_physical_source_energy_type_uniform_uniform_degree
    ε hε a₀ b₀ ha₀ windows M hM hwindowNorm hwindows
    W hWsupport hW kK kP kn kb η hkK hkP hkn hkb hη
  refine ⟨degree,?_⟩
  intro N a c mode s hc
  obtain ⟨C₀,C,Z₀,hC₀,hC,hZ₀,hsource⟩ := huniform (N:=N) (a:=a) (c:=c) (mode:=mode) s hc
  refine ⟨C₀,C,Z₀,hC₀,hC,hZ₀,?_⟩
  intro φ σ _ _ Z hZ X Y B L hX hY hB hL F jF hN hbase hac hF hNF hcharF hj
    u m T θ QK QP Qn Qb hT hQK hQP hQn hQb hsX hsY hsB hsL
    rows nset bset Pset S hrows E r₀ aw₀ w₀ hrowcop hproducts hScop hSN hSchar hn hb hP hr₀ haw₀ hw₀
  exact hsource Z hZ X Y B L hX hY hB hL F jF hN hbase hac hF hNF hcharF hj
    E.referencePrimes E.referenceArithmetic u m T θ QK QP Qn Qb hT hQK hQP hQn hQb hsX hsY hsB hsL
    rows nset bset Pset S hrows E.completion r₀ aw₀ w₀ hrowcop hproducts hScop hSN hSchar hn hb hP
    E.fixedFactor_eq E.cuspColumn_eq hr₀ haw₀ hw₀
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.LiteralNormalizedUniformDegree -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
universe u v

theorem sector_normalized_literal_energy_uniform_degree
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (η : ℝ) (hη : 0<η) :
    ∃ (degree : ℕ), ∀ {N a c : Eis} {mode : Bool}
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
    ∃ (C₀ C Z₀ : ℝ), 0≤C₀ ∧ 0<C ∧ 1<Z₀ ∧
    ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ Z : ℝ, Z₀≤Z →
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ),
      (9:Eis)*c∣N → (if mode then λ₀^2∣a-1 else λ₀^2∣c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis⧸F.ideal f)≠2) → (∀ f,jF f<6) →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=N) F rows Pset S hrows s hc),
      (∀ K∈rows,(∀ f,IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P∈Pset,(∏ j,(S P).ideal j)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ j,IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal j)) →
      (∀ P∈Pset,∀ j,ringChar (Eis⧸(F.sum (S P)).ideal j)≠2) →
    ∀ (u : Eisˣ) (i : ℕ×ℕ×ℕ) (T θ QK QP : ℝ) (r aw : Ideal Eis→ℂ),
      0<T → 1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      let branches := survivingFrozenBranches F jF (actualCuspColumn E.referenceArithmetic s hc u i.1)
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
      (∑ K : rows,‖literalDyadicRow F K.val (hrows K.val K.property) S jF Pset
        (E.completion K) s hc u i W θ T r aw‖^2)≤
      ((branches.card:ℝ)*∑ e∈branches,
        (Real.exp (Real.log 2/2+Real.log 2))^2*(6*C)*Z^(
          InverseTerminalWidths.reflectedExponent 0 (Real.logb Z QK)
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
            (Real.logb Z (QP/2))
            (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted F jF e 1)))
            (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted F jF e 2)))
            (InverseTerminalWidths.ramifiedWidth Z i.1)
            (InverseTerminalWidths.terminalDualWidth Z (Real.logb Z QK) (Real.logb Z (QP/2)) (Real.logb Z T) F.ideal jF e)+
          ε*(Real.logb Z QK+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted F jF e 1))+
            Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted F jF e 2))+Real.logb Z (QP/2))+η/2))*
        (C₀*(1+‖θ‖)^degree)^2 := by
  obtain ⟨degree,huniform⟩ := sector_normalized_physical_energy_uniform_degree
    ε hε lo hi hlo
    (fun _ => completedShellWindow) (fun _ => Real.log 2)
    (fun _ => Real.log_nonneg (by norm_num)) (fun _ => completedShellWindow_norm)
    (fun _ => completedShellWindow_support) W hWs hW 1 (1/2) 1 1 η
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hη
  refine ⟨degree,?_⟩
  intro N a c mode s hc
  obtain ⟨C₀,C,Z₀,hC₀,hC,hZ₀,henergy⟩ := huniform (N:=N) (a:=a) (c:=c) (mode:=mode) s hc
  refine ⟨C₀,C,Z₀,hC₀,hC,hZ₀,?_⟩
  intro φ σ _ _ Z hZ F jF hN hbase hac hF hNF hcharF hj rows Pset S hrows E
    hrowcop hprod hScop hSN hSchar u i T θ QK QP r aw hT hQK hQP hKr hPr hr haw
  have hkp : 0<QK := lt_of_lt_of_le zero_lt_one hQK
  have hpp : 0<QP := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hQP
  have hp : ∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤2*(QP/2) := by
    intro P hP
    simpa only [mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0)] using hPr P hP
  have hh := henergy Z hZ QK ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) (QP/2)
    hQK (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num)) (by linarith)
    F jF hN hbase hac hF hNF hcharF hj u i.1 T θ QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
    hT hkp hpp (by positivity) (by positivity) (by ring) (by ring) (by ring) (by ring)
    rows (reflectedNDyad i.2.2) (reflectedBDyad i.2.1) Pset S
    (fun K hK => ⟨hrows K hK,(hKr K hK).2⟩) E r aw (fun _ _ => 1)
    hrowcop hprod hScop hSN hSchar
    (fun n hn => ⟨(reflectedNDyad_bounds _ n hn).1,(reflectedNDyad_bounds _ n hn).2.2⟩)
    (fun b hb => ⟨(reflectedBDyad_bounds _ b hb).1,(reflectedBDyad_bounds _ b hb).2.2⟩)
    hp hr haw (fun _ _ => by simp)
  dsimp only at hh ⊢
  have he : (∑ K : rows,‖literalDyadicRow F K.val (hrows K.val K.property) S jF Pset
      (E.completion K) s hc u i W θ T r aw‖^2)=
      ∑ K : rows,‖weightedFinitePhysicalKernelRow F K.val (hrows K.val K.property) S jF Pset
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1) (E.completion K) s hc u i.1
        (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ T r aw (fun _ _ => 1)‖^2 := by
    apply Finset.sum_congr rfl
    intro K hK
    rw [literalDyadicRow_eq_physical F K.val (hrows K.val K.property) S jF Pset
      (E.completion K) s hc u i QK QP hkp hpp (hKr K.val K.property) hprod
      (fun P hP => (hPr P hP).2) W θ T r aw]
  rw [he]
  simpa only [Real.sqrt_one,mul_one] using hh
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.OriginalSectorUniformDegree -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem original_sector_literal_energy_uniform_degree
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η) :
    ∃ (degree : ℕ), ∀ {Nlevel a c₀ : Eis} {mode : Bool}
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (_hNlevel : (9:Eis)*c₀∣Nlevel)
    (_hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (_hac : IsCoprime a c₀),
    ∃ (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot : ℝ)
      (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤ margin → d≤ cstar/200 →
      η≤ cstar/1000 → δ+η≤ cstar/1000 → π≤ cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (u : Eisˣ) (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalDyadicRow G K.val (hrows K.val K.property) S j Pset
        (E.completion K) s hc₀ u i W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(F₀-cstar/4-O₀/2) := by
  obtain ⟨degree,huniform⟩ := sector_normalized_literal_energy_uniform_degree ε hε lo hi hlo W hWs hW η hηpos
  refine ⟨degree*2,?_⟩
  intro Nlevel a c₀ mode s hc₀ hNlevel hbase hac
  obtain ⟨C₀,Cs,Zs,hC₀,hCs,hZs,henergy⟩ := huniform (N:=Nlevel) (a:=a) (c:=c₀) (mode:=mode) s hc₀
  obtain ⟨Zb,Cb,hZb,hCb,hbranch⟩ := original_surviving_energy_sum s hc₀ ρ hρ 1 (1/2) η
    (by norm_num) (by norm_num) hηpos
  let Kc := (Real.exp (Real.log 2/2+Real.log 2))^2*(6*Cs)
  have hKc : 0<Kc := by dsimp [Kc];positivity
  refine ⟨Kc*Cb*C₀^2+1,max Zs Zb,by positivity,lt_of_lt_of_le hZs (le_max_left _ _),?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot i
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hret rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar u θ r aw hqk hqp hKr hPr hr haw
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZs ((le_max_left _ _).trans hZ))
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hpair := (poolPrimeFamily J (B*F*R) Q₀).restrict_pairwise (poolPrimeFamily_pairwise J (B*F*R) Q₀) A
  have hj : ∀ b : A,j b<6 := by intro b;exact Nat.mod_lt _ (by norm_num)
  have hs := henergy Z ((le_max_left _ _).trans hZ) G j hNlevel hbase hac hpair hGN hGchar hj
    rows Pset S hrows E hrowcop hprod hScop hSN hSchar u i X θ QK QP r aw hX hqk hqp hKr hPr hr haw
  have hb := hbranch J I F B R Q₀ hJ hI hF hB hR hpower hmask A (actualCuspColumn E.referenceArithmetic s hc₀ u i.1)
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP ε Lscale Lrow Lslot i
    ((le_max_right _ _).trans hZ) hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    (by simpa only [one_mul] using heH) (by simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using heza)
    heN hM hO hz hzcap hc hmargin hd hη hτ hπ hε.le
    (by simpa only [one_mul] using hrowcap) (by simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using hslotcap)
    hconst hbudget hscap hret
  dsimp only at hs hb
  rw [←heH,←heza,←heN] at hs
  simp_rw [←Finset.mul_sum] at hs
  apply hs.trans
  calc
    _ = Kc*((survivingFrozenBranches G j (actualCuspColumn E.referenceArithmetic s hc₀ u i.1)
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)).card*
      ∑ e∈survivingFrozenBranches G j (actualCuspColumn E.referenceArithmetic s hc₀ u i.1)
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1),
        Z^(InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
          (normWidth Z (frozenExtracted G j e 2)) za
          (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
          (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
          (ramifiedWidth Z i.1) (terminalDualWidth Z H za Nstar G.ideal j e)+
          ε*(H+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))+
            Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))+za)+η/2))*(C₀*(1+‖θ‖)^degree)^2 := by dsimp [Kc,G,j];ring
    _ ≤ Kc*(Cb*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(F₀-cstar/4-O₀/2))*(C₀*(1+‖θ‖)^degree)^2 := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hKc.le) (sq_nonneg _)
    _ = (Kc*Cb*C₀^2)*(1+‖θ‖)^(degree*2)*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(F₀-cstar/4-O₀/2) := by rw [mul_pow,←pow_mul];ring
    _ ≤ _ := by gcongr;linarith
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.OriginalRetainedUniformDegree -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem original_sector_retained_energy_uniform_degree
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η) :
    ∃ (degree : ℕ), ∀ {Nlevel a c₀ : Eis} {mode : Bool}
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (_hNlevel : (9:Eis)*c₀∣Nlevel)
    (_hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (_hac : IsCoprime a c₀),
    ∃ (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤ margin → d≤ cstar/200 →
      η≤ cstar/1000 → δ+η≤ cstar/1000 → π≤ cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ),
        literalDyadicRow G K.val (hrows K.val K.property) S j Pset
          (E.completion K) s hc₀ u i W θ X r aw‖^2)≤
        C*((retainedDyads (familyRawScale G s X QK QP) (16*Z^δ)).card:ℝ)^2*(1+‖θ‖)^degree*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(F₀-cstar/4-O₀/2) := by
  obtain ⟨degree,huniform⟩ := original_sector_literal_energy_uniform_degree ε hε lo hi hlo W hWs hW ρ hρ η hηpos
  refine ⟨degree,?_⟩
  intro Nlevel a c₀ mode s hc₀ hNlevel hbase hac
  obtain ⟨C,Z₀,hC,hZ₀,henergy⟩ := huniform (Nlevel:=Nlevel) (a:=a) (c₀:=c₀) (mode:=mode) s hc₀ hNlevel hbase hac
  refine ⟨36*C,Z₀,by positivity,hZ₀,?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let : Finite Eisˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Eisˣ := Fintype.ofFinite _
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let Dset := retainedDyads (familyRawScale G s X QK QP) (16*Z^δ)
  let src := fun (ui : Eisˣ×(ℕ×ℕ×ℕ)) (K : rows) =>
    literalDyadicRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ ui.1 ui.2 W θ X r aw
  have hb (ui : Eisˣ×(ℕ×ℕ×ℕ)) (hui : ui∈(Finset.univ:Finset Eisˣ)×ˢDset) :=
    henergy J I F B R Q₀ hJ hI hF hB hR hpower hmask A
      Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot ui.2
      hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
      heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hscap
      (Finset.mem_product.mp hui).2 rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar
      ui.1 θ r aw hqk hqp hKr hPr hr haw
  have hh := weighted_finite_row_energy_uniform ((Finset.univ:Finset Eisˣ)×ˢDset) (Finset.univ:Finset rows)
    (fun _ => (1:ℂ)) src _ hb
  have hcard : Fintype.card Eisˣ=6 := by
    rw [←Nat.card_eq_fintype_card]
    exact PrimaryIdealUnitReindex.card_units_eq_six
  simp only [src,one_mul,norm_one,Finset.sum_const,nsmul_eq_mul,mul_one,
    Finset.card_product,Finset.card_univ,hcard,Finset.sum_product,tsum_fintype] at hh ⊢
  apply hh.trans_eq
  push_cast
  ring
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.RetainedBudgetUniformDegree -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem original_sector_retained_budget_uniform_degree
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (_hLpool : 0≤Lpool) :
    ∃ (degree : ℕ), ∀ {Nlevel a c₀ : Eis} {mode : Bool}
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (_hNlevel : (9:Eis)*c₀∣Nlevel)
    (_hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (_hac : IsCoprime a c₀),
    ∃ (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤ margin → d≤ cstar/200 →
      η≤ cstar/1000 → δ+η≤ cstar/1000 → π≤ cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool → κ+ρ*Lpool≤ cstar/16 →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ),
        literalDyadicRow G K.val (hrows K.val K.property) S j Pset
          (E.completion K) s hc₀ u i W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2) := by
  obtain ⟨degree,huniform⟩ := original_sector_retained_energy_uniform_degree ε hε lo hi hlo W hWs hW ρ hρ η hηpos
  refine ⟨degree,?_⟩
  intro Nlevel a c₀ mode s hc₀ hNlevel hbase hac
  obtain ⟨C,Z₀,hC,hZ₀,henergy⟩ := huniform (Nlevel:=Nlevel) (a:=a) (c₀:=c₀) (mode:=mode) s hc₀ hNlevel hbase hac
  obtain ⟨Cd,hCd,hcount⟩ := retained_count_budget κ δ Lscale hκ hδL
  refine ⟨C*Cd,Z₀,mul_pos hC hCd,hZ₀,?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hpool hsmall rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  have hz' : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hzpos : 0<Z := lt_trans zero_lt_one hz'
  have hs := henergy J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hscap
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  have hd := hcount Z (familyRawScale G s X QK QP) hz'.le hscap
  have hp : (Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ≤Z^(Lpool*ρ) := by
    rw [Real.rpow_mul hzpos.le]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hpool hρ.le
  apply hs.trans
  calc
    _ ≤ C*(Cd*Z^κ)*(1+‖θ‖)^degree*Z^(Lpool*ρ)*Z^(F₀-cstar/4-O₀/2) := by gcongr
    _ = (C*Cd)*(1+‖θ‖)^degree*Z^(κ+Lpool*ρ+(F₀-cstar/4-O₀/2)) := by
      rw [Real.rpow_add hzpos,Real.rpow_add hzpos]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hz'.le (by nlinarith only [hsmall])) (by positivity)
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.WholeRow -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def literalWholeRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) : ℂ :=
  ∑ P : {P : Pset // IsCoprime K P.val}, r K*aw P.val.val*
    mixedReflectedValue (D P.val P.property) s (F.reflected K hK (S P.val.val)).generator_ne_zero hc
      (F.reflected K hK (S P.val.val)).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X

lemma sum_tsum_tsum_finite_middle {α β γ : Type*} [Fintype β]
    (L : Finset α) (f : α→β→γ→ℂ) (hf : ∀ p∈L, ∀ u, Summable (f p u)) :
    (∑ p∈L,∑' u,∑' i,f p u i)=∑' u,∑' i,∑ p∈L,f p u i := by
  simp only [tsum_fintype]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  exact (Summable.tsum_finsetSum (fun p hp => hf p hp u)).symm

theorem literalWholeRow_eq_dyadic (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ P∈Pset, ∀ i, ringChar (Eis⧸(F.reflected K hK (S P)).ideal i)≠2)
    (hj : ∀ i,jF i<6) (hprod : ∀ P∈Pset,(∏ j,(S P).ideal j)=P)
    (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo) (hWs : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (θ X : ℝ) (hX : 0<X) (r aw : Ideal Eis→ℂ) :
    literalWholeRow F K hK S jF Pset D s hc W θ X r aw=
      (fixedRadialCoefficientScalar*s.stratumShapeFactor (c*primaryGenerator (∏ i,F.ideal i)))*
        ∑' u : Eisˣ,∑' i : ℕ×ℕ×ℕ,
          literalDyadicRow F K hK S jF Pset D s hc u i W θ X
            (fun K => r K*shapeArgument (primaryGenerator K))
            (fun P => aw P*shapeArgument (primaryGenerator P)) := by
  let : Finite Eisˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Eisˣ := Fintype.ofFinite _
  have htw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) := by
    have he : (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ:ℝ→ℂ)=
        CompletedHeight.normTwistedSource W θ := by
      funext x
      exact CompletedHeight.uniformTwistedSchwartz_apply W lo hi hlo hWs hW θ x
    rw [←he]
    exact (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ).smooth ⊤
  have hts := (CompletedHeight.normTwistedSource_support W θ).trans hWs
  have hj' : ∀ i : φ ⊕ (PrimeIndex K ⊕ σ), reflectedExponent jF i<6 := by
    intro i
    rcases i with f | k | p
    · exact hj f
    · norm_num [reflectedExponent]
    · norm_num [reflectedExponent]
  let L := {P : Pset // IsCoprime K P.val}
  let block := fun (P : L) u i => literalDyadicBlock (F.reflected K hK (S P.val.val))
    (D P.val P.property) s hc (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ)
    (CompletedHeight.normTwistedSource W θ) X u i
  let wt := fun P : L => (r K*shapeArgument (primaryGenerator K))*(aw P.val.val*shapeArgument (primaryGenerator P.val.val))
  have hs (P : L) (u : Eisˣ) : Summable (fun i => wt P*block P u i) :=
    (literalDyadicBlock_summable (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) (reflectedExponent jF) hj' (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) lo hi hlo hts htw X hX u).mul_left _
  have hp (P : L) : r K*aw P.val.val*
      mixedReflectedValue (D P.val P.property) s (F.reflected K hK (S P.val.val)).generator_ne_zero hc
        (F.reflected K hK (S P.val.val)).generator_good (reflectedExponent jF)
        (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X=
      (fixedRadialCoefficientScalar*s.stratumShapeFactor (c*primaryGenerator (∏ i,F.ideal i)))*
        ∑' u : Eisˣ,∑' i : ℕ×ℕ×ℕ,wt P*block P u i := by
    rw [mixedReflectedValue_eq_dyadic (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) (reflectedExponent jF) hj' (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) lo hi hlo hts htw X hX,
      actual_shape_separation,hprod P.val.val P.val.property]
    simp only [tsum_mul_left]
    dsimp only [wt,block]
    ring
  unfold literalWholeRow
  simp_rw [hp]
  rw [←Finset.mul_sum,sum_tsum_tsum_finite_middle Finset.univ (fun P u i => wt P*block P u i) (fun P _ u => hs P u)]
  rfl
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.RowTail -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v
variable {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma finite_weighted_truncation {α β : Type*} [Fintype α]
    (f : α→β→ℂ) (w : α→ℂ) (J : Finset β)
    (hf : ∀ p, Summable (f p)) :
    (∑' i,∑ p,w p*f p i)-(∑ i∈J,∑ p,w p*f p i)=
      ∑ p,w p*((∑' i,f p i)-∑ i∈J,f p i) := by
  rw [Summable.tsum_finsetSum (fun p _ => (hf p).mul_left (w p)),Finset.sum_comm]
  simp only [tsum_mul_left,←Finset.mul_sum,mul_sub,Finset.sum_sub_distrib]

lemma finite_weighted_truncation_norm {α β : Type*} [Fintype α]
    (f : α→β→ℂ) (w : α→ℂ) (J : Finset β) (E : ℝ)
    (hf : ∀ p, Summable (f p)) (hw : ∀ p,‖w p‖≤1)
    (he : ∀ p, ‖(∑' i,f p i)-∑ i∈J,f p i‖≤E) :
    ‖(∑' i,∑ p,w p*f p i)-(∑ i∈J,∑ p,w p*f p i)‖≤Fintype.card α*E := by
  rw [finite_weighted_truncation f w J hf]
  calc
    _ ≤ ∑ p,‖w p*((∑' i,f p i)-∑ i∈J,f p i)‖ := norm_sum_le _ _
    _ ≤ ∑ _p : α,E := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hw p) (norm_nonneg _)).trans (by simpa using he p)
    _ = _ := by simp

theorem original_family_row_tail (lo hi : ℝ) (hlo : 0<lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0<C ∧
    ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ]
      (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
      (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
      (D : ∀ P : Pset, IsCoprime K P.val →
        ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ P∈Pset, ∀ i, ringChar (Eis⧸(F.reflected K hK (S P)).ideal i)≠2) →
      (∀ i,jF i<6) → (∀ P∈Pset,(∏ j,(S P).ideal j)=P) →
    ∀ (u : Eisˣ) (θ X T QK QP : ℝ) (r aw : Ideal Eis→ℂ),
      0<X → 0<T → 0<QK → 0<QP →
      (Ideal.absNorm K:ℝ)≤QK → (∀ P∈Pset,(Ideal.absNorm P:ℝ)≤QP) →
      ‖r K‖≤1 → (∀ P∈Pset,‖aw P‖≤1) →
      ‖(∑' i : ℕ×ℕ×ℕ,literalDyadicRow F K hK S jF Pset D s hc u i W θ X r aw)-
        ∑ i∈retainedDyads (familyRawScale F s X QK QP) (16*T),
          literalDyadicRow F K hK S jF Pset D s hc u i W θ X r aw‖≤
        Pset.card*(C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
          T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹) := by
  obtain ⟨degree,C,hC,hbound⟩ := original_family_dyadic_tail
    (N:=N) (a:=a) (c:=c) (mode:=mode) lo hi hlo A W hWs hW
  refine ⟨degree,C,hC,?_⟩
  intro φ σ _ _ F K hK S jF Pset D s hc hN hbase hchar hj hprod u θ X T QK QP r aw hX hT hQK hQP hKr hPr hr haw
  let L := {P : Pset // IsCoprime K P.val}
  let block := fun (P : L) i => literalDyadicBlock (F.reflected K hK (S P.val.val))
    (D P.val P.property) s hc (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ)
    (CompletedHeight.normTwistedSource W θ) X u i
  let J := retainedDyads (familyRawScale F s X QK QP) (16*T)
  have htw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) := by
    have he : (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ:ℝ→ℂ)=
        CompletedHeight.normTwistedSource W θ := by
      funext x
      exact CompletedHeight.uniformTwistedSchwartz_apply W lo hi hlo hWs hW θ x
    rw [←he]
    exact (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ).smooth ⊤
  have hj' : ∀ i : φ ⊕ (PrimeIndex K ⊕ σ), reflectedExponent jF i<6 := by
    intro i
    rcases i with f | k | p
    · exact hj f
    · norm_num [reflectedExponent]
    · norm_num [reflectedExponent]
  have hs (P : L) : Summable (block P) :=
    literalDyadicBlock_summable (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) (reflectedExponent jF) hj' (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) lo hi hlo
      ((CompletedHeight.normTwistedSource_support W θ).trans hWs) htw X hX u
  have he (P : L) : ‖(∑' i,block P i)-∑ i∈J,block P i‖≤
      C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
        T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹ := by
    rw [tsum_sub_finset_eq_tail (block P) (hs P) J]
    have hh := hbound F K hK (S P.val.val) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) jF hj u θ X T QK QP hX hT hQK hQP hKr
      (by rw [hprod P.val.val P.val.property]; exact hPr P.val.val P.val.property)
    apply le_trans ?_ hh
    apply le_of_eq
    congr 1
    apply tsum_congr
    intro i
    by_cases hi : i∈J <;> simp [J] at hi ⊢ <;> simp [hi,block]
  have hw (P : L) : ‖r K*aw P.val.val‖≤1 := by
    rw [norm_mul]
    exact (mul_le_mul hr (haw P.val.val P.val.property) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hh := finite_weighted_truncation_norm block (fun P : L => r K*aw P.val.val) J _ hs hw he
  change ‖(∑' i,∑ P : L,r K*aw P.val.val*block P i)-∑ i∈J,∑ P : L,r K*aw P.val.val*block P i‖≤_
  apply hh.trans
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast (Fintype.card_subtype_le (fun P : Pset => IsCoprime K P.val)).trans_eq (Fintype.card_coe Pset)
  · positivity
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.RowTailUniformDegree -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v

theorem original_family_row_tail_uniform_degree (lo hi : ℝ) (hlo : 0<lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0<C ∧
    ∀ {N a c : Eis} {mode : Bool}, ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ]
      (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
      (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
      (D : ∀ P : Pset, IsCoprime K P.val →
        ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ P∈Pset, ∀ i, ringChar (Eis⧸(F.reflected K hK (S P)).ideal i)≠2) →
      (∀ i,jF i<6) → (∀ P∈Pset,(∏ j,(S P).ideal j)=P) →
    ∀ (u : Eisˣ) (θ X T QK QP : ℝ) (r aw : Ideal Eis→ℂ),
      0<X → 0<T → 0<QK → 0<QP →
      (Ideal.absNorm K:ℝ)≤QK → (∀ P∈Pset,(Ideal.absNorm P:ℝ)≤QP) →
      ‖r K‖≤1 → (∀ P∈Pset,‖aw P‖≤1) →
      ‖(∑' i : ℕ×ℕ×ℕ,literalDyadicRow F K hK S jF Pset D s hc u i W θ X r aw)-
        ∑ i∈retainedDyads (familyRawScale F s X QK QP) (16*T),
          literalDyadicRow F K hK S jF Pset D s hc u i W θ X r aw‖≤
        Pset.card*(C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
          T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹) := by
  obtain ⟨degree,C,hC,hbound⟩ := original_family_dyadic_tail_uniform_degree lo hi hlo A W hWs hW
  refine ⟨degree,C,hC,?_⟩
  intro N a c mode φ σ _ _ F K hK S jF Pset D s hc hN hbase hchar hj hprod u θ X T QK QP r aw hX hT hQK hQP hKr hPr hr haw
  let L := {P : Pset // IsCoprime K P.val}
  let block := fun (P : L) i => literalDyadicBlock (F.reflected K hK (S P.val.val))
    (D P.val P.property) s hc (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ)
    (CompletedHeight.normTwistedSource W θ) X u i
  let J := retainedDyads (familyRawScale F s X QK QP) (16*T)
  have htw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) := by
    have he : (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ:ℝ→ℂ)=
        CompletedHeight.normTwistedSource W θ := by
      funext x
      exact CompletedHeight.uniformTwistedSchwartz_apply W lo hi hlo hWs hW θ x
    rw [←he]
    exact (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ).smooth ⊤
  have hj' : ∀ i : φ ⊕ (PrimeIndex K ⊕ σ), reflectedExponent jF i<6 := by
    intro i
    rcases i with f | k | p
    · exact hj f
    · norm_num [reflectedExponent]
    · norm_num [reflectedExponent]
  have hs (P : L) : Summable (block P) :=
    literalDyadicBlock_summable (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) (reflectedExponent jF) hj' (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) lo hi hlo
      ((CompletedHeight.normTwistedSource_support W θ).trans hWs) htw X hX u
  have he (P : L) : ‖(∑' i,block P i)-∑ i∈J,block P i‖≤
      C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
        T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹ := by
    rw [tsum_sub_finset_eq_tail (block P) (hs P) J]
    have hh := hbound F K hK (S P.val.val) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) jF hj u θ X T QK QP hX hT hQK hQP hKr
      (by rw [hprod P.val.val P.val.property]; exact hPr P.val.val P.val.property)
    apply le_trans ?_ hh
    apply le_of_eq
    congr 1
    apply tsum_congr
    intro i
    by_cases hi : i∈J <;> simp [J] at hi ⊢ <;> simp [hi,block]
  have hw (P : L) : ‖r K*aw P.val.val‖≤1 := by
    rw [norm_mul]
    exact (mul_le_mul hr (haw P.val.val P.val.property) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hh := finite_weighted_truncation_norm block (fun P : L => r K*aw P.val.val) J _ hs hw he
  change ‖(∑' i,∑ P : L,r K*aw P.val.val*block P i)-∑ i∈J,∑ P : L,r K*aw P.val.val*block P i‖≤_
  apply hh.trans
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast (Fintype.card_subtype_le (fun P : Pset => IsCoprime K P.val)).trans_eq (Fintype.card_coe Pset)
  · positivity
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.WholePair -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma sum_subtype_dite {α : Type*} [Fintype α] (p : α→Prop) (f : ∀ x,p x→ℂ) :
    (∑ x : {x // p x},f x.val x.property)=∑ x,if h:p x then f x h else 0 := by
  have hh := Fintype.sum_subtype_add_sum_subtype p (fun x => if h:p x then f x h else 0)
  have hz : (∑ x : {x // ¬p x},if h:p x.val then f x.val h else 0)=0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact dite_eq_right x.property
  rw [hz,add_zero] at hh
  simpa only [Subtype.property,dite_eq_left] using hh

def literalPairEntry (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows,Admissible K) (jF : φ→ℕ)
    (D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) (K P : Ideal Eis) : ℂ :=
  if hK:K∈rows then if hP:P∈Pset then if hp:IsCoprime K P then
    r K*aw P*mixedReflectedValue (D ⟨K,hK⟩ ⟨P,hP⟩ hp) s
      (F.reflected K (hrows K hK) (S P)).generator_ne_zero hc
      (F.reflected K (hrows K hK) (S P)).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X
  else 0 else 0 else 0

lemma literalWholeRow_eq_pairs (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows,Admissible K) (jF : φ→ℕ)
    (D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) (K : rows) :
    literalWholeRow F K.val (hrows K.val K.property) S jF Pset (D K) s hc W θ X r aw=
      ∑ P∈Pset,literalPairEntry F rows Pset S hrows jF D s hc W θ X r aw K.val P := by
  let f := fun (P : Pset) (hp : IsCoprime K.val P.val) => r K.val*aw P.val*
    mixedReflectedValue (D K P hp) s (F.reflected K.val (hrows K.val K.property) (S P.val)).generator_ne_zero hc
      (F.reflected K.val (hrows K.val K.property) (S P.val)).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K.val) σ) (CompletedHeight.normTwistedSource W θ) X
  change (∑ P : {P : Pset // IsCoprime K.val P.val},f P.val P.property)=_
  rw [sum_subtype_dite (fun P : Pset => IsCoprime K.val P.val) f,
    ←Finset.sum_coe_sort Pset (literalPairEntry F rows Pset S hrows jF D s hc W θ X r aw K.val)]
  apply Finset.sum_congr rfl
  intro P hP
  simp only [literalPairEntry,dite_eq_left K.property,dite_eq_left P.property,f]

lemma literalPairEntry_restrict (F : PrimeFamily φ) (rows Pset rows' Pset' : Finset (Ideal Eis))
    (hrow : rows'⊆rows) (hP : Pset'⊆Pset) (S : Ideal Eis→PrimeFamily σ)
    (hrows : ∀ K∈rows,Admissible K) (jF : φ→ℕ)
    (D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (E : SectorArithmetic (N:=N) F rows' Pset' S (fun K hK => hrows K (hrow hK)) s hc)
    (hE : ∀ (K : rows') (P : Pset') hp,E.completion K P hp=D ⟨K.val,hrow K.property⟩ ⟨P.val,hP P.property⟩ hp)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) (K P : Ideal Eis) (hK : K∈rows') (hp : P∈Pset') :
    literalPairEntry F rows' Pset' S (fun K hK => hrows K (hrow hK)) jF E.completion s hc W θ X r aw K P=
      literalPairEntry F rows Pset S hrows jF D s hc W θ X r aw K P := by
  simp only [literalPairEntry,dite_eq_left hK,dite_eq_left hp,dite_eq_left (hrow hK),dite_eq_left (hP hp)]
  by_cases hcop : IsCoprime K P
  · simp only [dite_eq_left hcop,hE]
  · simp only [dite_eq_right hcop]
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.ActiveProducts -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma slotProductCoefficient_norm (tuples : Finset (σ→Ideal Eis))
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
    (aw : (σ→Ideal Eis)→ℂ) (haw : ∀ p∈tuples,‖aw p‖≤1)
    (P : Ideal Eis) (hP : P∈tuples.image slotTupleProduct) :
    ‖slotProductCoefficient tuples aw P‖≤1 := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hP
  rw [slotProductCoefficient_at_product tuples hinj aw p hp]
  exact haw p hp

def activeTupleReflectedRow
    (F : PrimeFamily φ) (rows : Finset (Ideal Eis))
    (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
    (hrows : ∀ K∈rows,Admissible K) (jF : φ→ℕ)
    (D : ∀ K : rows,∀ P : tuples.image slotTupleProduct,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property)
        (tuplePrimeFamily tuples hne hmax hgood P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ) (K : rows) : ℂ :=
    ∑ p : tuples,if hp:IsCoprime K.val (slotTupleProduct p.val) then
      r K.val*aw p.val*mixedReflectedValue
        (D K ⟨slotTupleProduct p.val,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩ hp) s
        (F.reflected K.val (hrows K.val K.property) (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val))).generator_ne_zero hc
        (F.reflected K.val (hrows K.val K.property) (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val))).generator_good
        (reflectedExponent jF) (slotIndices φ (PrimeIndex K.val) σ)
        (CompletedHeight.normTwistedSource W θ) X else 0

theorem literalWholeRow_eq_active_tuples
    (F : PrimeFamily φ) (rows : Finset (Ideal Eis))
    (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
    (hrows : ∀ K∈rows,Admissible K) (jF : φ→ℕ)
    (D : ∀ K : rows,∀ P : tuples.image slotTupleProduct,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property)
        (tuplePrimeFamily tuples hne hmax hgood P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ) (K : rows) :
    literalWholeRow F K.val (hrows K.val K.property) (tuplePrimeFamily tuples hne hmax hgood)
      jF (tuples.image slotTupleProduct) (D K) s hc W θ X r (slotProductCoefficient tuples aw)=
    ∑ p : tuples,if hp:IsCoprime K.val (slotTupleProduct p.val) then
      r K.val*aw p.val*mixedReflectedValue
        (D K ⟨slotTupleProduct p.val,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩ hp) s
        (F.reflected K.val (hrows K.val K.property) (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val))).generator_ne_zero hc
        (F.reflected K.val (hrows K.val K.property) (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val))).generator_good
        (reflectedExponent jF) (slotIndices φ (PrimeIndex K.val) σ)
        (CompletedHeight.normTwistedSource W θ) X else 0 := by
  rw [literalWholeRow_eq_pairs F rows _ _ hrows jF D s hc W θ X r _ K,Finset.sum_image hinj]
  rw [←Finset.sum_coe_sort tuples]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [literalPairEntry,dite_eq_left K.property,
    dite_eq_left (Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩),
    slotProductCoefficient_at_product tuples hinj aw p.val p.property]
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.FixedTuples -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ : Type*} [Fintype σ] [DecidableEq σ]

def fixedSlotTupleSet (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis) : Finset (σ→Ideal Eis) :=
  (Fintype.piFinset L).filter fun p => ∀ j i,p i≠F j

lemma mem_fixedSlotTupleSet (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis) (p : σ→Ideal Eis) :
    p∈fixedSlotTupleSet L F ↔ (∀ i,p i∈L i) ∧ ∀ j i,p i≠F j := by
  simp only [fixedSlotTupleSet,Finset.mem_filter,Fintype.mem_piFinset]

lemma fixedSlotTupleSet_product_injective (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j))) (hprime : ∀ i,∀ P∈L i,Prime P) :
    Set.InjOn slotTupleProduct (↑(fixedSlotTupleSet L F) : Set (σ→Ideal Eis)) :=
  (slotTupleProduct_injective_on L hL hprime).mono (fun p hp => (mem_fixedSlotTupleSet L F p).mp hp |>.1)

def supportedSlotTupleEquiv (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis) (K : Ideal Eis) :
    supportedSlotChoices L F K ≃ {p : fixedSlotTupleSet L F // IsCoprime K (slotTupleProduct p.val)} where
  toFun p := ⟨⟨fun i => (p.val i).val,(mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩⟩,p.property.1⟩
  invFun p := ⟨fun i => ⟨p.val.val i,((mem_fixedSlotTupleSet L F _).mp p.val.property).1 i⟩,
    ⟨p.property,((mem_fixedSlotTupleSet L F _).mp p.val.property).2⟩⟩
  left_inv p := by
    apply Subtype.ext
    funext i
    rfl
  right_inv p := rfl

def supportedSlotProductEquiv (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j))) (hprime : ∀ i,∀ P∈L i,Prime P)
    (K : Ideal Eis) :
    supportedSlotChoices L F K ≃
      {P : (fixedSlotTupleSet L F).image slotTupleProduct // IsCoprime K P.val} := by
  let f := fun p : supportedSlotChoices L F K =>
    (⟨⟨slotTupleProduct (fun i => (p.val i).val),Finset.mem_image.mpr
      ⟨fun i => (p.val i).val,(mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩,rfl⟩⟩,p.property.1⟩ :
      {P : (fixedSlotTupleSet L F).image slotTupleProduct // IsCoprime K P.val})
  apply Equiv.ofBijective f
  constructor
  · intro p q he
    have hv := congrArg (fun P => P.val.val) he
    have hh := fixedSlotTupleSet_product_injective L F hL hprime
      ((mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩)
      ((mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (q.val i).property,q.property.2⟩) hv
    apply Subtype.ext
    funext i
    exact Subtype.ext (congrFun hh i)
  · intro P
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp P.val.property
    let q : supportedSlotChoices L F K := ⟨fun i => ⟨p i,((mem_fixedSlotTupleSet L F p).mp hp).1 i⟩,
      ⟨by change IsCoprime K (slotTupleProduct p);rw [he];exact P.property,((mem_fixedSlotTupleSet L F p).mp hp).2⟩⟩
    refine ⟨q,?_⟩
    apply Subtype.ext
    exact Subtype.ext he

lemma supportedSlotProductEquiv_apply (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j))) (hprime : ∀ i,∀ P∈L i,Prime P)
    (K : Ideal Eis) (p : supportedSlotChoices L F K) :
    ((supportedSlotProductEquiv L F hL hprime K) p).val.val=∏ i,(p.val i).val := rfl
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.ChoiceTransport -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]

def fixedTupleFamily (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hne : (fixedSlotTupleSet L F).Nonempty)
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P) (P : Ideal Eis) : PrimeFamily σ :=
  tuplePrimeFamily (fixedSlotTupleSet L F) hne
    (fun p hp i => hmax i _ (((mem_fixedSlotTupleSet L F p).mp hp).1 i))
    (fun p hp i => hgood i _ (((mem_fixedSlotTupleSet L F p).mp hp).1 i)) P

lemma fixedTupleFamily_at_choice (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hne : (fixedSlotTupleSet L F).Nonempty)
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j))) (hprime : ∀ i,∀ P∈L i,Prime P)
    (p : ∀ i,L i) (hp : ∀ j i,(p i).val≠F j) :
    fixedTupleFamily L F hne hmax hgood (∏ i,(p i).val)=slotChoiceFamily L hmax hgood p := by
  apply PrimeFamily.eq_of_ideal_eq
  exact tuplePrimeFamily_at_product (fixedSlotTupleSet L F) hne _ _
    (fixedSlotTupleSet_product_injective L F hL hprime) (fun i => (p i).val)
    ((mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p i).property,hp⟩)

def fixedTupleCoefficient (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ) (p : σ→Ideal Eis) : ℂ :=
  if hp:∀ i,p i∈L i then ∏ i,w i ⟨p i,hp i⟩ else 0

omit [DecidableEq σ] in
lemma fixedTupleCoefficient_at (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ) (p : ∀ i,L i) :
    fixedTupleCoefficient L w (fun i => (p i).val)=∏ i,w i (p i) := by
  simp only [fixedTupleCoefficient,dite_eq_left (show ∀ i,(p i).val∈L i from fun i => (p i).property)]

omit [DecidableEq σ] in
lemma fixedTupleCoefficient_norm (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ)
    (hw : ∀ i P,‖w i P‖≤1) (p : σ→Ideal Eis) : ‖fixedTupleCoefficient L w p‖≤1 := by
  unfold fixedTupleCoefficient
  split
  · exact slot_coefficient_norm L w hw _
  · simp

variable {N a c : Eis} {mode : Bool}
variable (G : PrimeFamily τ) (K : Ideal Eis) (hK : Admissible K)
    (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hne : (fixedSlotTupleSet L F).Nonempty)
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j))) (hprime : ∀ i,∀ P∈L i,Prime P)
    (D : ∀ P : (fixedSlotTupleSet L F).image slotTupleProduct,IsCoprime K P.val→
      ControlledStratumArithmetic (G.reflected K hK (fixedTupleFamily L F hne hmax hgood P.val)).generator N a c mode)
    (p : supportedSlotChoices L F K)

def activeChoiceControlled :
      ControlledStratumArithmetic (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator N a c mode :=
  castControlled (congrArg (fun S => (G.reflected K hK S).generator)
    (fixedTupleFamily_at_choice L F hne hmax hgood hL hprime p.val p.property.2))
    (D ⟨∏ i,(p.val i).val,Finset.mem_image.mpr
      ⟨fun i => (p.val i).val,(mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩,rfl⟩⟩ p.property.1)

lemma activeChoiceControlled_value
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : τ→ℕ) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (activeChoiceControlled G K hK L F hne hmax hgood hL hprime D p) s
      (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_ne_zero hc
      (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_good
      (reflectedExponent j) (slotIndices τ (PrimeIndex K) σ) W X=
    mixedReflectedValue (D ⟨∏ i,(p.val i).val,Finset.mem_image.mpr
      ⟨fun i => (p.val i).val,(mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩,rfl⟩⟩ p.property.1) s
      (G.reflected K hK (fixedTupleFamily L F hne hmax hgood (∏ i,(p.val i).val))).generator_ne_zero hc
      (G.reflected K hK (fixedTupleFamily L F hne hmax hgood (∏ i,(p.val i).val))).generator_good
      (reflectedExponent j) (slotIndices τ (PrimeIndex K) σ) W X := by
  exact mixedReflectedValue_cast _ _ s _ _ hc _ _ _ _ W X

theorem literalWholeRow_eq_original_choices
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : τ→ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (w : ∀ i,L i→ℂ) :
    literalWholeRow G K hK (fixedTupleFamily L F hne hmax hgood) j
      ((fixedSlotTupleSet L F).image slotTupleProduct) D s hc W θ X r
      (slotProductCoefficient (fixedSlotTupleSet L F) (fixedTupleCoefficient L w))=
    ∑ p : supportedSlotChoices L F K,r K*(∏ i,w i (p.val i))*
      mixedReflectedValue (activeChoiceControlled G K hK L F hne hmax hgood hL hprime D p) s
        (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_ne_zero hc
        (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_good
        (reflectedExponent j) (slotIndices τ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X := by
  let e := supportedSlotProductEquiv L F hL hprime K
  unfold literalWholeRow
  rw [←e.sum_comp]
  apply Finset.sum_congr rfl
  intro p hp
  rw [activeChoiceControlled_value G K hK L F hne hmax hgood hL hprime D p s hc j]
  have hcft : slotProductCoefficient (fixedSlotTupleSet L F) (fixedTupleCoefficient L w)
      (e p).val.val=∏ i,w i (p.val i) := by
    change slotProductCoefficient (fixedSlotTupleSet L F) (fixedTupleCoefficient L w)
      (slotTupleProduct (fun i => (p.val i).val))=_
    rw [slotProductCoefficient_at_product (fixedSlotTupleSet L F)
      (fixedSlotTupleSet_product_injective L F hL hprime) (fixedTupleCoefficient L w)
      (fun i => (p.val i).val) ((mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩)]
    exact fixedTupleCoefficient_at L w p.val
  rw [hcft]
  rfl

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.GlobalEnergy -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma fullRaySector_subset (N : Eis) (rows : Finset (Ideal Eis)) (r : Eis⧸Ideal.span {N^2}) :
    fullRaySector N rows r⊆rows := Finset.filter_subset _ _

theorem literal_global_sector_energy [Fintype (Eis⧸Ideal.span {N^2})]
    (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows,Admissible K) (jF : φ→ℕ)
    (D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) (B : ℝ)
    (hsector : ∀ r₀ p₀ : Eis⧸Ideal.span {N^2},
      ∃ E : SectorArithmetic (N:=N) F (fullRaySector N rows r₀) (fullRaySector N Pset p₀) S
        (fun K hK => hrows K (fullRaySector_subset N rows r₀ hK)) s hc,
        (∀ (K : fullRaySector N rows r₀) (P : fullRaySector N Pset p₀) hp,
          E.completion K P hp=D ⟨K.val,(fullRaySector_subset N rows r₀ K.property)⟩
            ⟨P.val,(fullRaySector_subset N Pset p₀ P.property)⟩ hp) ∧
        (∑ K : fullRaySector N rows r₀,‖literalWholeRow F K.val
          (hrows K.val (fullRaySector_subset N rows r₀ K.property)) S jF (fullRaySector N Pset p₀)
          (E.completion K) s hc W θ X r aw‖^2)≤B) :
    (∑ K : rows,‖literalWholeRow F K.val (hrows K.val K.property) S jF Pset
      (D K) s hc W θ X r aw‖^2)≤(Fintype.card (Eis⧸Ideal.span {N^2}):ℝ)^3*B := by
  let f := literalPairEntry F rows Pset S hrows jF D s hc W θ X r aw
  have hs (r₀ p₀ : Eis⧸Ideal.span {N^2}) :
      (∑ K∈fullRaySector N rows r₀,‖∑ P∈fullRaySector N Pset p₀,f K P‖^2)≤B := by
    obtain ⟨E,hE,hbound⟩ := hsector r₀ p₀
    have he : (∑ K : fullRaySector N rows r₀,‖literalWholeRow F K.val
          (hrows K.val (fullRaySector_subset N rows r₀ K.property)) S jF (fullRaySector N Pset p₀)
          (E.completion K) s hc W θ X r aw‖^2)=
        ∑ K∈fullRaySector N rows r₀,‖∑ P∈fullRaySector N Pset p₀,f K P‖^2 := by
      let fl := literalPairEntry F (fullRaySector N rows r₀) (fullRaySector N Pset p₀) S
        (fun K hK => hrows K (fullRaySector_subset N rows r₀ hK)) jF E.completion s hc W θ X r aw
      calc
        _ = ∑ K : fullRaySector N rows r₀,‖∑ P∈fullRaySector N Pset p₀,fl K.val P‖^2 := by
          apply Finset.sum_congr rfl
          intro K hK
          apply congrArg (fun z : ℂ => ‖z‖^2)
          exact literalWholeRow_eq_pairs F (fullRaySector N rows r₀) (fullRaySector N Pset p₀) S
            (fun K hK => hrows K (fullRaySector_subset N rows r₀ hK)) jF E.completion s hc W θ X r aw K
        _ = ∑ K∈fullRaySector N rows r₀,‖∑ P∈fullRaySector N Pset p₀,fl K P‖^2 :=
          Finset.sum_coe_sort _ (fun K => ‖∑ P∈fullRaySector N Pset p₀,fl K P‖^2)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro K hK
          apply congrArg (fun z : ℂ => ‖z‖^2)
          apply Finset.sum_congr rfl
          intro P hP
          exact literalPairEntry_restrict F rows Pset (fullRaySector N rows r₀) (fullRaySector N Pset p₀)
            (fullRaySector_subset N rows r₀) (fullRaySector_subset N Pset p₀) S hrows jF D s hc E hE W θ X r aw K P hK hP
    rw [←he]
    exact hbound
  have hh := full_ray_sector_energy N rows Pset f B hs
  have he : (∑ K : rows,‖literalWholeRow F K.val (hrows K.val K.property) S jF Pset
      (D K) s hc W θ X r aw‖^2)=∑ K∈rows,‖∑ P∈Pset,f K P‖^2 := by
    calc
      _ = ∑ K : rows,‖∑ P∈Pset,f K.val P‖^2 := by
        apply Finset.sum_congr rfl
        intro K hK
        exact congrArg (fun z : ℂ => ‖z‖^2) (literalWholeRow_eq_pairs F rows Pset S hrows jF D s hc W θ X r aw K)
      _ = _ := Finset.sum_coe_sort rows (fun K => ‖∑ P∈Pset,f K P‖^2)
  rw [he]
  exact hh
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.MarkedTuples -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
lemma sum_subtype_dite_decidable {α : Type*} [Fintype α] (p : α→Prop) [DecidablePred p]
    (f : ∀ x,p x→ℂ) :
    (∑ x : {x // p x},f x.val x.property)=∑ x,if h:p x then f x h else 0 := by
  have hh := Fintype.sum_subtype_add_sum_subtype p (fun x => if h:p x then f x h else 0)
  have hz : (∑ x : {x // ¬p x},if h:p x.val then f x.val h else 0)=0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact dite_eq_right x.property
  rw [hz,add_zero] at hh
  simpa only [Subtype.property,dite_eq_left] using hh

variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime (Q*Ideal.span {(72:Eis)}) (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable {α : Type*} [Fintype α] (Sp : α→PrimeFamily σ)
local notation "E" => D.primeFiberEquiv R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad

include hR hI hF hm hf hz hbad hcop hpow hmask

theorem actual_marked_tuple_reflection
    (hS : ∀ p,Pairwise (Function.onFun IsCoprime (Sp p).ideal))
    (hSodd : ∀ p i,ringChar (Eis⧸(Sp p).ideal i)≠2)
    (Ψ : Eis→*ℂ) (hΨnorm : ∀ n,‖Ψ n‖≤1) (hQ : Q≠0)
    (hΨperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h,(9:Eis)*(G h).c0∣N)
    (hNp : ∀ p i,IsCoprime (Ideal.span {N}) ((markedRowFamily D (Sp p) Q).ideal i))
    (C : ∀ p : {p : α // ∀ P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)}),∀ i,(Sp p).ideal i≠P.val.val},
      ∀ h : Eis⧸Ideal.span {c},∀ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
      ∀ T : Finset σ,ControlledStratumArithmetic
        (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected K hK ((Sp p.val).restrict T)).generator
        N (G h).a0 (G h).c0 (G h).mode)
    (w : α→ℂ) (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    (∑ p : α,w p*markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (Sp p).ideal i∣A then (1:ℂ) else 0))=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h*
      ∑ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),∑ T : Finset σ,
        frozenInactiveWeight R F (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}) A*
        ∑ p : {p : α // ∀ P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)}),∀ i,(Sp p).ideal i≠P.val.val},
          (∏ t∈(Finset.univ:Finset σ)\T,(Ideal.absNorm ((Sp p.val).ideal t):ℂ)⁻¹)*w p.val*
          mixedReflectedValue (C p h A T) (G h).shape
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected K hK ((Sp p.val).restrict T)).generator_ne_zero
            (G h).denominator_ne_zero
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected K hK ((Sp p.val).restrict T)).generator_good
            (reflectedExponent (fun b : A => completedLocalExponent R F b.val.val))
            (slotIndices A (PrimeIndex K) T) W X := by
  let good := fun p : α => ∀ P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)}),∀ i,(Sp p).ideal i≠P.val.val
  let row := fun p : α => markedCompletedT (rowTwist Ψ m f z) W X
    (fun A => ∏ i,if (Sp p).ideal i∣A then (1:ℂ) else 0)
  have hzrow (p : α) (hp : ¬good p) : row p=0 := by
    simp only [good,not_forall,not_not] at hp
    obtain ⟨P,i,he⟩ := hp
    exact actual_marked_row_overlap_zero D (Sp p) Ψ Q hmLam hm2 P i he W X
  have hrestrict : (∑ p : α,w p*row p)=∑ p : {p // good p},w p.val*row p.val := by
    calc
      _ = ∑ p : α,if h:good p then w p*row p else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hg : good p
        · rw [dite_eq_left hg]
        · rw [dite_eq_right hg,hzrow p hg,mul_zero]
      _ = _ := (sum_subtype_dite_decidable good (fun p _ => w p*row p)).symm
  change (∑ p : α,w p*row p)=_
  rw [hrestrict]
  have he (p : {p // good p}) := actual_marked_selected_reflection D R I F Q hR hI hF hm hf hz hbad hcop hpow hmask
    (Sp p.val) (hS p.val) (hSodd p.val) p.property Ψ hΨnorm hQ hΨperiod hmLam hm2 c hc hcQ G N hN
    (hNp p.val) (C p) W hWcompact lo hi hlo hsupp hW X hX
  dsimp only [row]
  simp_rw [he]
  simp only [Finset.mul_sum,frozenInactiveWeight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro p hp
  ring
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.InactiveSource -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ : Type*} [Fintype σ] [DecidableEq σ]

lemma supported_inactive_sum_eq (rows : Finset (Ideal Eis))
    (L : σ→Finset (Ideal Eis)) (T : Finset σ) (F : φ→Ideal Eis)
    (K : rows) (w : ∀ i,L i→ℂ)
    (f : supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val→ℂ) :
    (∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*f b)=
    ∑ b : ∀ i : {i // i∉T},L i.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b i)))*
        (if hk:K.val∈inactiveRowSet rows L T F b then f ⟨b,(Finset.mem_filter.mp hk).2⟩ else 0) := by
  let ok := fun b : ∀ i : {i // i∉T},L i.val =>
    IsCoprime K.val (∏ i : {i // i∉T},(b i).val) ∧ ∀ j i,(b i).val≠F j
  let wt := fun b : ∀ i : {i // i∉T},L i.val =>
    (∏ i : {i // i∉T},(Ideal.absNorm (b i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b i))
  have he := sum_subtype_dite_decidable ok (fun b hb => wt b*f ⟨b,hb⟩)
  change (∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val,wt b.val*f b)=_
  calc
    _ = ∑ b,if hb:ok b then wt b*f ⟨b,hb⟩ else 0 := he
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hc : ok b
      · have hk : K.val∈inactiveRowSet rows L T F b := Finset.mem_filter.mpr ⟨K.property,hc⟩
        simp only [dite_eq_left hc,dite_eq_left hk,wt]
      · have hk : K.val∉inactiveRowSet rows L T F b := fun h => hc (Finset.mem_filter.mp h).2
        simp only [dite_eq_right hc,dite_eq_right hk,mul_zero]

theorem supported_inactive_source_energy (rows : Finset (Ideal Eis))
    (L : σ→Finset (Ideal Eis)) (T : Finset σ) (F : φ→Ideal Eis) (H : σ→ℝ)
    (hzero : ∀ i,∀ P∈L i,P≠0) (hH : ∀ i,∀ P∈L i,(Ideal.absNorm P:ℝ)≤H i)
    (w : ∀ i,L i→ℂ) (hw : ∀ i P,‖w i P‖≤1)
    (f : ∀ K : rows,supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val→ℂ)
    (E : ℝ) (hE : 0≤E)
    (hf : ∀ b : ∀ i : {i // i∉T},L i.val,
      (∑ K : inactiveRowSet rows L T F b,
        ‖f ⟨K.val,(Finset.mem_filter.mp K.property).1⟩ ⟨b,(Finset.mem_filter.mp K.property).2⟩‖^2)≤E) :
    (∑ K : rows,‖∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*f K b‖^2)≤
    (∏ i : {i // i∉T},256*(columnDyadicLength (H i.val)+1:ℝ))^2*E := by
  let g := fun (b : ∀ i : {i // i∉T},L i.val) (K : inactiveRowSet rows L T F b) =>
    f ⟨K.val,(Finset.mem_filter.mp K.property).1⟩ ⟨b,(Finset.mem_filter.mp K.property).2⟩
  have he := original_inactive_restricted_energy rows L T F H hzero hH w hw g E hE hf
  have hh : (∑ K : rows,‖∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*f K b‖^2)=
      ∑ K∈rows,‖∑ b : ∀ i : {i // i∉T},L i.val,
        ((∏ i : {i // i∉T},(Ideal.absNorm (b i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b i)))*
          (if hk:K∈inactiveRowSet rows L T F b then g b ⟨K,hk⟩ else 0)‖^2 := by
    rw [←Finset.sum_coe_sort rows]
    apply Finset.sum_congr rfl
    intro K hK
    rw [supported_inactive_sum_eq rows L T F K w (f K)]
  exact hh.trans_le he
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.OriginalSplitReflection -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime (Q*Ideal.span {(72:Eis)}) (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)

theorem actual_marked_slot_split_reflection
    (hS : ∀ p : ∀ i,L i,Pairwise (Function.onFun IsCoprime (slotChoiceFamily L hmax hgood p).ideal))
    (hSodd : ∀ p : ∀ i,L i,∀ i,ringChar (Eis⧸(slotChoiceFamily L hmax hgood p).ideal i)≠2)
    (Ψ : Eis→*ℂ) (hΨnorm : ∀ n,‖Ψ n‖≤1) (hQ : Q≠0)
    (hΨperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h,(9:Eis)*(G h).c0∣N)
    (hNp : ∀ p : ∀ i,L i,∀ i,IsCoprime (Ideal.span {N}) ((markedRowFamily D (slotChoiceFamily L hmax hgood p) Q).ideal i))
    (C : ∀ p : originalSlotChoices D (Q*Ideal.span {(72:Eis)}) L,
      ∀ h : Eis⧸Ideal.span {c},∀ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
      ∀ T : Finset σ,ControlledStratumArithmetic
        (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator
        N (G h).a0 (G h).c0 (G h).mode)
    (w : ∀ i,L i→ℂ) (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    (∑ p : ∀ i,L i,(∏ i,w i (p i))*markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (slotChoiceFamily L hmax hgood p).ideal i∣A then (1:ℂ) else 0))=
    let physical := fun (h : Eis⧸Ideal.span {c})
      (A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})))
      (T : Finset σ) (p : originalSlotChoices D (Q*Ideal.span {(72:Eis)}) L) =>
      mixedReflectedValue (C p h A T) (G h).shape
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_ne_zero
            (G h).denominator_ne_zero
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_good
            (reflectedExponent (fun b : A => completedLocalExponent R F b.val.val))
            (slotIndices A (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h*
      ∑ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
        frozenInactiveWeight R F (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}) A*
        ∑ T : Finset σ,
          ∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
            ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal)
            (rowResidualPart I (Ideal.span {m}*F)),
            ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*
              ∑ a : supportedSlotChoices (fun i : T => L i.val)
                ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal)
                (rowResidualPart I (Ideal.span {m}*F)),
                (∏ i : T,w i.val (a.val i))*physical h A T
                  ((originalSlotSplit D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T).symm (b,a)) := by
  dsimp only
  rw [actual_marked_tuple_reflection D R I F Q hR hI hF hm hf hz hbad hcop hpow hmask
    (fun p : ∀ i,L i => slotChoiceFamily L hmax hgood p) hS hSodd Ψ hΨnorm hQ hΨperiod hmLam hm2
    c hc hcQ G N hN hNp C (fun p => ∏ i,w i (p i)) W hWcompact lo hi hlo hsupp hW X hX]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  congr 1
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  congr 1
  have hs :=
    (original_supported_slot_sum D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask
      L hmax hgood T w (fun p => mixedReflectedValue (C p h A T) (G h).shape
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_ne_zero
            (G h).denominator_ne_zero
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_good
            (reflectedExponent (fun b : A => completedLocalExponent R F b.val.val))
            (slotIndices A (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X))
  convert hs using 1
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  congr 1
  apply Finset.prod_congr (by ext; simp only [Finset.mem_sdiff,Finset.mem_univ])
  intro t ht
  rfl

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.OriginalActiveReflection -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime (Q*Ideal.span {(72:Eis)}) (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)

include hR hI hF hm hf hz hbad hcop hpow hmask

theorem actual_marked_active_reflection
    (hS : ∀ p : ∀ i,L i,Pairwise (Function.onFun IsCoprime (slotChoiceFamily L hmax hgood p).ideal))
    (hSodd : ∀ p : ∀ i,L i,∀ i,ringChar (Eis⧸(slotChoiceFamily L hmax hgood p).ideal i)≠2)
    (Ψ : Eis→*ℂ) (hΨnorm : ∀ n,‖Ψ n‖≤1) (hQ : Q≠0)
    (hΨperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h,(9:Eis)*(G h).c0∣N)
    (hNp : ∀ p : ∀ i,L i,∀ i,IsCoprime (Ideal.span {N}) ((markedRowFamily D (slotChoiceFamily L hmax hgood p) Q).ideal i))
    (C : ∀ h : Eis⧸Ideal.span {c},
      ∀ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
      ∀ T : Finset σ,
      ∀ _b : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ∀ p : supportedSlotChoices (fun i : T => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ControlledStratumArithmetic
        (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected
          (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
          (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator
        N (G h).a0 (G h).c0 (G h).mode)
    (w : ∀ i,L i→ℂ) (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    (∑ p : ∀ i,L i,(∏ i,w i (p i))*markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (slotChoiceFamily L hmax hgood p).ideal i∣A then (1:ℂ) else 0))=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h*
      ∑ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
        frozenInactiveWeight R F (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}) A*
        ∑ T : Finset σ,
          ∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
            ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal)
            (rowResidualPart I (Ideal.span {m}*F)),
            ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*
              ∑ a : supportedSlotChoices (fun i : T => L i.val)
                ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal)
                (rowResidualPart I (Ideal.span {m}*F)),
                (∏ i : T,w i.val (a.val i))*
                  originalSplitPhysical R I F (Q*Ideal.span {(72:Eis)}) hbad L hmax hgood
                    ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A)
                    T (C h A T) (G h).shape (G h).denominator_ne_zero
                    (fun b : A => completedLocalExponent R F b.val.val) W X (b,a) := by
  let Call := fun (p : originalSlotChoices D (Q*Ideal.span {(72:Eis)}) L)
    (h : Eis⧸Ideal.span {c})
    (A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}))) (T : Finset σ) =>
      originalSplitControlled D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood
        ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A) T (C h A T) p
  rw [actual_marked_slot_split_reflection D R I F Q hR hI hF hm hf hz hbad hcop hpow hmask
    L hmax hgood hS hSodd Ψ hΨnorm hQ hΨperiod hmLam hm2 c hc hcQ G N hN hNp Call
    w W hWcompact lo hi hlo hsupp hW X hX]
  dsimp only
  apply congrArg (fun z : ℂ => thetaDerivativeScalar⁻¹*z)
  apply Finset.sum_congr rfl
  intro h hh
  apply congrArg (fun z : ℂ => fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h*z)
  apply Finset.sum_congr rfl
  intro A hA
  apply congrArg (fun z : ℂ => frozenInactiveWeight R F (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}) A*z)
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro b hb
  apply congrArg (fun z : ℂ =>
    ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*z)
  apply Finset.sum_congr rfl
  intro a ha
  apply congrArg (fun z : ℂ => (∏ i : T,w i.val (a.val i))*z)
  dsimp only [Call]
  have hv := originalSplitControlled_physical D R I F (Q*Ideal.span {(72:Eis)})
    hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood
    ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A) T (C h A T)
    ((originalSlotSplit D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T).symm (b,a))
    (G h).shape (G h).denominator_ne_zero (fun b : A => completedLocalExponent R F b.val.val) W X
  exact hv.trans (congrArg
    (originalSplitPhysical R I F (Q*Ideal.span {(72:Eis)}) hbad L hmax hgood
      ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A) T (C h A T)
      (G h).shape (G h).denominator_ne_zero (fun b : A => completedLocalExponent R F b.val.val) W X)
    ((originalSlotSplit D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T).apply_symm_apply (b,a)))

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.PunctureAbsorption -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem rowTwist_absorb_puncture (Ψ : Eis→*ℂ) (m B f z : Eis)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (hΨzero : ∀ n,¬IsCoprime B n → Ψ n=0) :
    rowTwist Ψ (m*B) f z=rowTwist Ψ m f z := by
  ext n
  by_cases hn : Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask Ψ (m*B) f z n hn,rowTwist_extract_sixth_mask Ψ m f z n hn]
    by_cases hb : IsCoprime B n
    · change Ψ n*(if IsCoprime (m*B) n then (1:ℂ) else 0)*_=
        Ψ n*(if IsCoprime m n then (1:ℂ) else 0)*_
      simp only [IsCoprime.mul_left_iff,hb,and_true]
    · rw [hΨzero n hb]
      simp only [zero_mul]
  · rw [rowTwist_zero_of_not_supported Ψ (m*B) f z n
        (dvd_mul_of_dvd_left hmLam B) (dvd_mul_of_dvd_left hm2 B) hn,
      rowTwist_zero_of_not_supported Ψ m f z n hmLam hm2 hn]

lemma markedCompletedT_absorb_puncture (Ψ : Eis→*ℂ) (m B f z : Eis)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (hΨzero : ∀ n,¬IsCoprime B n → Ψ n=0)
    (W : ℝ→ℂ) (X : ℝ) (mark : Ideal Eis→ℂ) :
    markedCompletedT (rowTwist Ψ (m*B) f z) W X mark=
      markedCompletedT (rowTwist Ψ m f z) W X mark := by
  rw [rowTwist_absorb_puncture Ψ m B f z hmLam hm2 hΨzero]

lemma rowResidualPart_coprime_period (I F Q : Ideal Eis) (m : Eis)
    (hQ : Q∣Ideal.span {m}) :
    IsCoprime Q (rowResidualPart I (Ideal.span {m}*F)) := by
  exact (squarefreeResidualPart_coprime (rowSimplePart I) (Ideal.span {m}*F)).symm.of_isCoprime_of_dvd_left
    (dvd_mul_of_dvd_left hQ F)

lemma rowResidualPart_coprime_enlarged_period (I F Q : Ideal Eis) (m B : Eis)
    (hQ : Q∣Ideal.span {B}) :
    IsCoprime Q (rowResidualPart I (Ideal.span {m*B}*F)) := by
  apply rowResidualPart_coprime_period I F Q (m*B)
  rw [←Ideal.span_singleton_mul_span_singleton]
  exact dvd_mul_of_dvd_right hQ _

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.PuncturedMarks -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma markedCompletedT_zero_punctured (Ψ : Eis→*ℂ) (m f z : Eis)
    (P : Ideal Eis) (hP : Prime P) (hm : m∈P)
    (W : ℝ→ℂ) (X : ℝ) (d : Ideal Eis→ℂ) (hd : ∀ A,¬P∣A → d A=0) :
    markedCompletedT (rowTwist Ψ m f z) W X d=0 := by
  have hz (I J : Ideal Eis) : summand (rowTwist Ψ m f z) W X I J*d (I*J^3)=0 := by
    by_cases hdiv : P∣I*J^3
    · rcases hP.dvd_mul.mp hdiv with hI|hJ
      · have hz := CanonicalRowCompletion.columnWeight_zero_of_mask Ψ m f z hP hI hm
        simp only [summand,hz,zero_div,zero_mul]
      · have hz := cubeWeight_zero_of_prime_mask Ψ m f z hP (hP.dvd_of_dvd_pow hJ) hm
        simp only [summand,hz,mul_zero,zero_mul]
    · rw [hd _ hdiv,mul_zero]
  simp only [markedCompletedT,hz,tsum_zero]

lemma markedCompletedT_zero_punctured_slot {σ : Type*} [Fintype σ]
    (S : PrimeFamily σ) (i : σ) (Ψ : Eis→*ℂ) (m f z : Eis) (hm : m∈S.ideal i)
    (W : ℝ→ℂ) (X : ℝ) :
    markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ j,if S.ideal j∣A then (1:ℂ) else 0)=0 := by
  apply markedCompletedT_zero_punctured Ψ m f z (S.ideal i)
    (Ideal.prime_of_isPrime (NeZero.ne (S.ideal i)) inferInstance) hm W X
  intro A hA
  exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hA)
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.OriginalRetainedSlots -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {α σ : Type*} [Fintype σ]

def punctureRetainedTuples (tuples : Finset α) (S : α→PrimeFamily σ) (m : Eis) : Finset α :=
  tuples.filter (fun p => ∀ i,m∉(S p).ideal i)

theorem original_tuple_filter_puncture (tuples : Finset α) (S : α→PrimeFamily σ)
    (w : α→ℂ) (Ψ : Eis→*ℂ) (m f z : Eis) (W : ℝ→ℂ) (X : ℝ) :
    (∑ p∈tuples,w p*markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (S p).ideal i∣A then (1:ℂ) else 0))=
    ∑ p∈punctureRetainedTuples tuples S m,w p*markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (S p).ideal i∣A then (1:ℂ) else 0) := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hpbad
  have hh : ¬∀ i,m∉(S p).ideal i := fun h => hpbad (Finset.mem_filter.mpr ⟨hp,h⟩)
  push Not at hh
  obtain ⟨i,hi⟩ := hh
  rw [markedCompletedT_zero_punctured_slot (S p) i Ψ m f z hi W X,mul_zero]

lemma retained_slot_period (tuples : Finset α) (S : α→PrimeFamily σ)
    (m : Eis) (Q : Ideal Eis) (hQ : Q∣Ideal.span {m})
    (p : α) (hp : p∈punctureRetainedTuples tuples S m) (i : σ) :
    IsCoprime Q ((S p).ideal i) := by
  apply (maximal_coprime_of_not_dvd _ _ ?_).symm
  intro h
  have hd := dvd_trans h hQ
  exact (Finset.mem_filter.mp hp).2 i ((Ideal.dvd_iff_le.mp hd) (Ideal.subset_span (by simp)))

lemma retained_markedRowFamily_period {m f z : Eis} (D : GoodMaskRowData m f z)
    (tuples : Finset α) (S : α→PrimeFamily σ) (Q : Ideal Eis) (c : Eis)
    (hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (hpuncture : Q*Ideal.span {(72:Eis)}∣Ideal.span {m})
    (p : α) (hp : p∈punctureRetainedTuples tuples S m) :
    ∀ i,IsCoprime (Ideal.span {(9:Eis)*c}) ((markedRowFamily D (S p) Q).ideal i) := by
  exact markedRowFamily_period D (S p) Q
    (fun i => retained_slot_period tuples S m _ hpuncture p hp i) c hcQ

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.PunctureLists -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def punctureLists (lists : σ→Finset (Ideal Eis)) (S : Finset (Ideal Eis)) : σ→Finset (Ideal Eis) :=
  fun i => (lists i).filter (fun P => P∉S)

def punctureListLift (lists : σ→Finset (Ideal Eis)) (S : Finset (Ideal Eis))
    (p : ∀ i,punctureLists lists S i) : ∀ i,lists i :=
  fun i => ⟨(p i).val,(Finset.mem_filter.mp (p i).property).1⟩

def punctureListEquiv (lists : σ→Finset (Ideal Eis)) (S : Finset (Ideal Eis)) :
    (∀ i,punctureLists lists S i) ≃ {p : ∀ i,lists i // ∀ i,(p i).val∉S} where
  toFun p := ⟨punctureListLift lists S p,fun i => (Finset.mem_filter.mp (p i).property).2⟩
  invFun p i := ⟨(p.val i).val,Finset.mem_filter.mpr ⟨(p.val i).property,p.property i⟩⟩
  left_inv _p := rfl
  right_inv _p := rfl

lemma sum_puncture_lists (lists : σ→Finset (Ideal Eis)) (S : Finset (Ideal Eis))
    (f : (∀ i,lists i)→ℂ) (hz : ∀ p,(∃ i,(p i).val∈S) → f p=0) :
    (∑ p : ∀ i,lists i,f p)=∑ p : ∀ i,punctureLists lists S i,f (punctureListLift lists S p) := by
  have he := (punctureListEquiv lists S).sum_comp (fun p => f p.val)
  have hs := sum_subtype_dite_decidable (fun p : ∀ i,lists i => ∀ i,(p i).val∉S) (fun p _ => f p)
  calc
    _ = ∑ p : ∀ i,lists i,if h:∀ i,(p i).val∉S then f p else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs with h
      · rfl
      · exact hz p (by simpa only [not_forall,not_not] using h)
    _ = ∑ p : {p : ∀ i,lists i // ∀ i,(p i).val∉S},f p.val := hs.symm
    _ = _ := he.symm

theorem original_completed_puncture_lists (lists : σ→Finset (Ideal Eis))
    (hprime : ∀ i,∀ P∈lists i,Prime P) (S : Finset (Ideal Eis))
    (Ψ : Eis→*ℂ) (m f z : Eis) (W : ℝ→ℂ) (X : ℝ) (w : ∀ i,lists i→ℂ) :
    (∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ (m*excludedGenerator S) f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0))=
    ∑ p : ∀ i,punctureLists lists S i,(∏ i,w i (punctureListLift lists S p i))*markedCompletedT
      (rowTwist Ψ (m*excludedGenerator S) f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0) := by
  apply sum_puncture_lists lists S
  intro p hp
  obtain ⟨i,hi⟩ := hp
  have hm : m*excludedGenerator S∈(p i).val := (p i).val.mul_mem_left m (excludedGenerator_mem S hi)
  have hz := markedCompletedT_zero_punctured Ψ (m*excludedGenerator S) f z (p i).val
    (hprime i _ (p i).property) hm W X (fun A => ∏ j,if (p j).val∣A then (1:ℂ) else 0)
    (fun A hA => Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hA))
  exact mul_eq_zero_of_right _ hz
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.LowPunctureLists -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def actualPuncturePrimes (lists : σ→Finset (Ideal Eis)) (m : Eis) : Finset (Ideal Eis) :=
  (Finset.univ.biUnion lists).filter (fun P => m∈P)

omit [DecidableEq σ] in
lemma actualPuncturePrimes_mem (lists : σ→Finset (Ideal Eis)) (m : Eis)
    (i : σ) (P : Ideal Eis) (hP : P∈lists i) :
    P∈actualPuncturePrimes lists m ↔ m∈P := by
  simp only [actualPuncturePrimes,Finset.mem_filter]
  exact and_iff_right (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hP⟩)

lemma puncture_period_coprime (Q : Ideal Eis) (m : Eis) (hQ : Q∣Ideal.span {m})
    (P : Ideal Eis) (hP : P.IsMaximal) (hm : m∉P) : IsCoprime Q P := by
  let : P.IsMaximal := hP
  have hp : ¬P∣Ideal.span {m} := by
    intro h
    exact hm ((Ideal.dvd_iff_le.mp h) (Ideal.subset_span (Set.mem_singleton m)))
  exact (maximal_coprime_of_not_dvd P (Ideal.span {m}) hp).symm.of_isCoprime_of_dvd_left hQ

theorem original_completed_actual_puncture_lists (lists : σ→Finset (Ideal Eis))
    (hprime : ∀ i,∀ P∈lists i,Prime P)
    (Ψ : Eis→*ℂ) (m f z : Eis) (W : ℝ→ℂ) (X : ℝ) (w : ∀ i,lists i→ℂ) :
    (∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0))=
    ∑ p : ∀ i,punctureLists lists (actualPuncturePrimes lists m) i,
      (∏ i,w i (punctureListLift lists (actualPuncturePrimes lists m) p i))*markedCompletedT
      (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0) := by
  apply sum_puncture_lists lists (actualPuncturePrimes lists m)
  intro p hp
  obtain ⟨i,hi⟩ := hp
  have hm : m∈(p i).val := (Finset.mem_filter.mp hi).2
  have hz := markedCompletedT_zero_punctured Ψ m f z (p i).val
    (hprime i _ (p i).property) hm W X (fun A => ∏ j,if (p j).val∣A then (1:ℂ) else 0)
    (fun A hA => Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hA))
  exact mul_eq_zero_of_right _ hz
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.TupleDyads -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def activeTupleDyad (tuples : Finset (σ→Ideal Eis)) (H : ℝ)
    (i : Fin (columnDyadicLength H+1)) : Finset (σ→Ideal Eis) :=
  tuples.filter fun p => divisorDyadicLabel H (slotTupleProduct p)=i

omit [DecidableEq σ] in
lemma sum_activeTupleDyads {A : Type*} [AddCommMonoid A]
    (tuples : Finset (σ→Ideal Eis)) (H : ℝ) (f : (σ→Ideal Eis)→A) :
    (∑ p∈tuples,f p)=∑ i : Fin (columnDyadicLength H+1),∑ p∈activeTupleDyad tuples H i,f p := by
  exact (Finset.sum_fiberwise tuples (fun p => divisorDyadicLabel H (slotTupleProduct p)) f).symm

omit [DecidableEq σ] in
lemma activeTupleDyad_bounds (tuples : Finset (σ→Ideal Eis)) (H : ℝ)
    (hn : ∀ p∈tuples,1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤H)
    (i : Fin (columnDyadicLength H+1)) (p : σ→Ideal Eis) (hp : p∈activeTupleDyad tuples H i) :
    divisorDyadicScale i.val≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧
      (Ideal.absNorm (slotTupleProduct p):ℝ)≤2*divisorDyadicScale i.val := by
  obtain ⟨hpt,he⟩ := Finset.mem_filter.mp hp
  have hh := divisorDyadicLabel_bounds H (slotTupleProduct p) (hn p hpt).1 (hn p hpt).2
  rw [he] at hh
  constructor
  · exact max_le (hn p hpt).1 hh.1.le
  · have ht : (2:ℝ)^i.val/2≤divisorDyadicScale i.val := le_max_right _ _
    linarith [hh.2]

omit [DecidableEq σ] in
lemma activeTupleDyad_scale_le (tuples : Finset (σ→Ideal Eis)) (H : ℝ)
    (hn : ∀ p∈tuples,1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤H)
    (i : Fin (columnDyadicLength H+1)) (hi : (activeTupleDyad tuples H i).Nonempty) :
    divisorDyadicScale i.val≤H := by
  obtain ⟨p,hp⟩ := hi
  exact (activeTupleDyad_bounds tuples H hn i p hp).1.trans (hn p (Finset.mem_filter.mp hp).1).2

omit [DecidableEq σ] in
lemma activeTupleDyad_width (tuples : Finset (σ→Ideal Eis)) (H Z z : ℝ)
    (hZ : 1<Z) (hH : H≤Z^z)
    (hn : ∀ p∈tuples,1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤H)
    (i : Fin (columnDyadicLength H+1)) (hi : (activeTupleDyad tuples H i).Nonempty) :
    0≤Real.logb Z (divisorDyadicScale i.val) ∧ Real.logb Z (divisorDyadicScale i.val)≤z := by
  have hs := divisorDyadicScale_ge_one i.val
  have hp : 0<divisorDyadicScale i.val := lt_of_lt_of_le zero_lt_one hs
  constructor
  · have hh := Real.logb_le_logb_of_le hZ zero_lt_one hs
    simpa only [Real.logb_one] using hh
  · have hh := Real.logb_le_logb_of_le hZ hp ((activeTupleDyad_scale_le tuples H hn i hi).trans hH)
    rwa [Real.logb_rpow (lt_trans zero_lt_one hZ) (ne_of_gt hZ)] at hh
omit [DecidableEq σ] in
lemma slotTupleProduct_norm_bound (L : σ→Finset (Ideal Eis)) (H : σ→ℝ)
    (hzero : ∀ i,∀ P∈L i,P≠0) (hH : ∀ i,∀ P∈L i,(Ideal.absNorm P:ℝ)≤H i)
    (p : σ→Ideal Eis) (hp : ∀ i,p i∈L i) :
    1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤∏ i,H i := by
  have hn : slotTupleProduct p≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hzero i _ (hp i))
  refine ⟨QuadraticMainBoundary.norm_one_le hn,?_⟩
  change (Ideal.absNorm (∏ i,p i):ℝ)≤_
  rw [map_prod,Nat.cast_prod]
  exact Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hH i _ (hp i))

omit [DecidableEq σ] in
lemma activeTupleDyad_energy_scale (tuples : Finset (σ→Ideal Eis)) (H Z z : ℝ)
    (hZ : 1<Z) (hH : H≤Z^z)
    (hn : ∀ p∈tuples,1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤H)
    (i : Fin (columnDyadicLength H+1)) (hi : (activeTupleDyad tuples H i).Nonempty) :
    2≤2*divisorDyadicScale i.val ∧
      0≤Real.logb Z ((2*divisorDyadicScale i.val)/2) ∧
      Real.logb Z ((2*divisorDyadicScale i.val)/2)≤z ∧
      ∀ p∈activeTupleDyad tuples H i,
        (2*divisorDyadicScale i.val)/2≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧
          (Ideal.absNorm (slotTupleProduct p):ℝ)≤2*divisorDyadicScale i.val := by
  have hw := activeTupleDyad_width tuples H Z z hZ hH hn i hi
  have hs := divisorDyadicScale_ge_one i.val
  rw [show (2*divisorDyadicScale i.val)/2=divisorDyadicScale i.val by ring]
  exact ⟨by linarith,hw.1,hw.2,activeTupleDyad_bounds tuples H hn i⟩

end
end SevenEighths.InverseReflectedPhase

end OAI

end

