module
public import Swanepoel.FaceDualConnectivityLinear
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def PennyGraph.contactGradient {n : ℕ} (G : PennyGraph n) :
    (Fin n → ℝ) →ₗ[ℝ] (ContactEdge G → ℝ) where
  toFun f e := f e.val.2-f e.val.1
  map_add' f g := by ext e; simp only [Pi.add_apply]; ring
  map_smul' c f := by ext e; simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring

@[simp] theorem PennyGraph.contactGradient_apply {n : ℕ} (G : PennyGraph n)
    (f : Fin n → ℝ) (e : ContactEdge G) :
    G.contactGradient f e = f e.val.2-f e.val.1 := rfl

theorem PennyGraph.contactGradient_zero_adj {n : ℕ} (G : PennyGraph n)
    (f : Fin n → ℝ) (hf : G.contactGradient f = 0) {a b : Fin n} (hab : G.graph.Adj a b) :
    f a = f b := by
  rcases lt_or_gt_of_ne hab.ne with hlt | hlt
  · have he := congrFun hf (⟨(a,b),hlt,hab⟩ : ContactEdge G)
    change f b-f a = 0 at he
    exact (sub_eq_zero.mp he).symm
  · have he := congrFun hf (⟨(b,a),hlt,hab.symm⟩ : ContactEdge G)
    change f a-f b = 0 at he
    exact sub_eq_zero.mp he

theorem PennyGraph.contactGradient_zero_reachable {n : ℕ} (G : PennyGraph n)
    (f : Fin n → ℝ) (hf : G.contactGradient f = 0) {a b : Fin n} (hab : G.graph.Reachable a b) :
    f a = f b := by
  obtain ⟨q⟩ := hab
  induction q with
  | nil => rfl
  | cons h q ih => exact (G.contactGradient_zero_adj f hf h).trans ih

theorem PennyGraph.contactGradient_zero_iff_constant {n : ℕ} (G : PennyGraph n)
    (hc : G.graph.Connected) (f : Fin n → ℝ) :
    G.contactGradient f = 0 ↔ ∃ c : ℝ, f = fun _ => c := by
  constructor
  · intro hf
    obtain ⟨a⟩ := hc.nonempty
    refine ⟨f a,?_⟩
    ext b
    exact G.contactGradient_zero_reachable f hf (hc b a)
  · rintro ⟨c,rfl⟩
    ext e
    simp only [PennyGraph.contactGradient_apply,sub_self,Pi.zero_apply]

theorem PennyGraph.contactGradient_ker {n : ℕ} (G : PennyGraph n) (hc : G.graph.Connected) :
    LinearMap.ker G.contactGradient = Submodule.span ℝ {fun _ : Fin n => (1 : ℝ)} := by
  ext f
  rw [LinearMap.mem_ker,G.contactGradient_zero_iff_constant hc,Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c,rfl⟩
    refine ⟨c,?_⟩
    ext a
    simp
  · rintro ⟨c,hc⟩
    refine ⟨c,?_⟩
    rw [← hc]
    ext a
    simp

theorem PennyGraph.contactGradient_ker_finrank {n : ℕ} (G : PennyGraph n)
    (hc : G.graph.Connected) : Module.finrank ℝ (LinearMap.ker G.contactGradient) = 1 := by
  rw [G.contactGradient_ker hc]
  apply finrank_span_singleton
  obtain ⟨a⟩ := hc.nonempty
  intro he
  have ha := congrFun he a
  norm_num at ha

theorem PennyGraph.contactGradient_range_finrank_add_one {n : ℕ} (G : PennyGraph n)
    (hc : G.graph.Connected) : Module.finrank ℝ (LinearMap.range G.contactGradient)+1 = n := by
  have h := G.contactGradient.finrank_range_add_finrank_ker
  rwa [G.contactGradient_ker_finrank hc,Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at h

theorem PennyGraph.contactGradient_range_finrank {n : ℕ} (G : PennyGraph n)
    (hc : G.graph.Connected) : Module.finrank ℝ (LinearMap.range G.contactGradient) = n-1 := by
  have h := G.contactGradient_range_finrank_add_one hc
  omega

def PennyGraph.contactGradientL2 {n : ℕ} (G : PennyGraph n) :
    (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (ContactEdge G) :=
  (WithLp.linearEquiv 2 ℝ (ContactEdge G → ℝ)).symm.toLinearMap.comp G.contactGradient

@[simp] theorem PennyGraph.contactGradientL2_apply {n : ℕ} (G : PennyGraph n)
    (f : Fin n → ℝ) (e : ContactEdge G) :
    G.contactGradientL2 f e = f e.val.2-f e.val.1 := rfl

theorem PennyGraph.contactGradientL2_ker {n : ℕ} (G : PennyGraph n) :
    LinearMap.ker G.contactGradientL2 = LinearMap.ker G.contactGradient := by
  ext f
  change (G.contactGradientL2 f = 0) ↔ G.contactGradient f = 0
  constructor
  · intro he
    ext e
    exact congrArg (fun z : EuclideanSpace ℝ (ContactEdge G) => z e) he
  · intro he
    ext e
    exact congrFun he e

theorem PennyGraph.contactGradientL2_range_finrank_add_one {n : ℕ} (G : PennyGraph n)
    (hc : G.graph.Connected) : Module.finrank ℝ (LinearMap.range G.contactGradientL2)+1 = n := by
  have h := G.contactGradientL2.finrank_range_add_finrank_ker
  rwa [G.contactGradientL2_ker,G.contactGradient_ker_finrank hc,
    Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at h

def PennyGraph.contactCycleSpace {n : ℕ} (G : PennyGraph n) : Submodule ℝ (EuclideanSpace ℝ (ContactEdge G)) :=
  (LinearMap.range G.contactGradientL2)ᗮ

theorem PennyGraph.contactCycleSpace_finrank_add_vertices {n : ℕ} (G : PennyGraph n)
    (hc : G.graph.Connected) : Module.finrank ℝ G.contactCycleSpace+n = G.edgeCount+1 := by
  have h := (LinearMap.range G.contactGradientL2).finrank_add_finrank_orthogonal
  rw [finrank_euclideanSpace,G.contactEdge_count] at h
  have hr := G.contactGradientL2_range_finrank_add_one hc
  change Module.finrank ℝ (LinearMap.range G.contactGradientL2)+Module.finrank ℝ G.contactCycleSpace =
    G.edgeCount at h
  omega

end Swanepoel
