module
public import Swanepoel.RhombicFaceEnumeration
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Topology.Algebra.Module.FiniteDimension
@[expose] public section

noncomputable section
namespace Swanepoel

abbrev PlaneFace {n : ℕ} (G : PennyGraph n) := {F : Set Plane // G.IsFace F}

theorem PennyGraph.IsFace.isOpen {n : ℕ} {G : PennyGraph n} {F : Set Plane}
    (hf : G.IsFace F) : IsOpen F := by
  obtain ⟨z,_,rfl⟩ := hf
  exact G.isClosed_drawing.isOpen_compl.connectedComponentIn

theorem PennyGraph.IsFace.nonempty {n : ℕ} {G : PennyGraph n} {F : Set Plane}
    (hf : G.IsFace F) : F.Nonempty := by
  obtain ⟨z,hz,rfl⟩ := hf
  exact ⟨z,mem_connectedComponentIn hz⟩

theorem PennyGraph.IsFace.eq_component {n : ℕ} {G : PennyGraph n} {F : Set Plane}
    (hf : G.IsFace F) {z : Plane} (hz : z∈F) : F=connectedComponentIn G.drawingᶜ z := by
  obtain ⟨w,_,rfl⟩ := hf
  exact connectedComponentIn_eq hz

theorem dense_finite_intersection {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (s : ι → Set X) (ho : ∀ i, IsOpen (s i)) (hd : ∀ i, Dense (s i)) : Dense (⋂ i, s i) := by
  classical
  have h (A : Finset ι) : Dense (⋂ i ∈ A, s i) := by
    induction A using Finset.induction_on with
    | empty => simp
    | @insert i A _ ih =>
      have he : (⋂ j ∈ insert i A, s j)=s i ∩ ⋂ j ∈ A, s j := by ext x; simp
      rw [he]
      exact (hd i).inter_of_isOpen_left ih (ho i)
  simpa using h Finset.univ

theorem dense_complement_affine_line (l : Plane →ₗ[ℝ] ℝ) (hl : l≠0) (c : ℝ) :
    Dense {z | l z≠c} := by
  have hex : ∃ w, l w≠0 := by
    by_contra hn
    push Not at hn
    exact hl (LinearMap.ext hn)
  obtain ⟨w,hw⟩ := hex
  have hsurj : Function.Surjective l := by
    intro r
    refine ⟨(r/l w) • w,?_⟩
    rw [map_smul,smul_eq_mul,div_mul_cancel₀ _ hw]
  exact (dense_compl_singleton c).preimage (l.isOpenMap_of_finiteDimensional hsurj)

theorem positive_weighted_average {a b x y : ℝ} (ha : 0≤a) (hb : 0≤b) (hab : a+b=1)
    (hx : 0<x) (hy : 0<y) : 0<a*x+b*y := by
  rcases eq_or_lt_of_le ha with he | he
  · have hz : a=0 := he.symm
    rw [hz,zero_mul,zero_add]
    exact mul_pos (by linarith) hy
  · exact add_pos_of_pos_of_nonneg (mul_pos he hx) (mul_nonneg hb hy.le)

theorem finite_faces_of_affine_cover {n : ℕ} (G : PennyGraph n) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (l : ι → Plane →ₗ[ℝ] ℝ) (c : ι → ℝ)
    (hl : ∀ i, l i≠0) (hcover : ∀ z∈G.drawing, ∃ i, l i z=c i) : Finite (PlaneFace G) := by
  classical
  let general : Set Plane := {z | ∀ i, l i z≠c i}
  have hgeneral : Dense general := by
    have h := dense_finite_intersection (fun i => {z : Plane | l i z≠c i})
      (fun i => isOpen_ne.preimage (l i).continuous_of_finiteDimensional)
      (fun i => dense_complement_affine_line (l i) (hl i) (c i))
    simpa only [Set.iInter_ofPred] using h
  let signature (z : Plane) : Finset ι := Finset.univ.filter (fun i => c i<l i z)
  let cell (A : Finset ι) : Set Plane := {z | ∀ i, if i∈A then c i<l i z else l i z<c i}
  have hmem (z : Plane) (hz : z∈general) : z∈cell (signature z) := by
    intro i
    by_cases hi : c i<l i z
    · simp [signature,hi]
    · have hlt : l i z<c i := lt_of_le_of_ne (le_of_not_gt hi) (hz i)
      simp [signature,hi,hlt]
  have hconvex (A : Finset ι) : Convex ℝ (cell A) := by
    intro x hx y hy a b ha hb hab i
    have he : l i (a • x+b • y)-c i=a*(l i x-c i)+b*(l i y-c i) := by
      rw [map_add,map_smul,map_smul]
      change a*l i x+b*l i y-c i=a*(l i x-c i)+b*(l i y-c i)
      linear_combination (c i)*hab
    by_cases hi : i∈A
    · have hx' : c i<l i x := by simpa only [ite_eq_left hi] using hx i
      have hy' : c i<l i y := by simpa only [ite_eq_left hi] using hy i
      have hh := positive_weighted_average ha hb hab (sub_pos.mpr hx') (sub_pos.mpr hy')
      simpa only [ite_eq_left hi] using (show c i<l i (a • x+b • y) by linarith)
    · have hx' : l i x<c i := by simpa only [ite_eq_right hi] using hx i
      have hy' : l i y<c i := by simpa only [ite_eq_right hi] using hy i
      have hh := positive_weighted_average ha hb hab (sub_pos.mpr hx') (sub_pos.mpr hy')
      simpa only [ite_eq_right hi] using (show l i (a • x+b • y)<c i by nlinarith)
  have hcell (A : Finset ι) : cell A⊆G.drawingᶜ := by
    intro z hz hdraw
    obtain ⟨i,hi⟩ := hcover z hdraw
    have hh := hz i
    by_cases hia : i∈A
    · simp only [ite_eq_left hia,hi,lt_self_iff_false] at hh
    · simp only [ite_eq_right hia,hi,lt_self_iff_false] at hh
  have hpoint (F : PlaneFace G) : ∃ z, z∈F.val ∧ z∈general :=
    hgeneral.inter_open_nonempty F.val F.property.isOpen F.property.nonempty
  choose p hpF hpL using hpoint
  apply Finite.of_injective (fun F : PlaneFace G => signature (p F))
  intro F H hsig
  change signature (p F)=signature (p H) at hsig
  have hF : p F∈cell (signature (p F)) := hmem _ (hpL F)
  have hH : p H∈cell (signature (p F)) := by rw [hsig]; exact hmem _ (hpL H)
  have hcomp := (hconvex (signature (p F))).isPreconnected.subset_connectedComponentIn hF
    (hcell (signature (p F))) hH
  apply Subtype.ext
  rw [F.property.eq_component (hpF F),H.property.eq_component (hpF H)]
  exact connectedComponentIn_eq hcomp

def coordinateLinear : Plane →ₗ[ℝ] ℝ where
  toFun z := z 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def crossLinear (v : Plane) : Plane →ₗ[ℝ] ℝ where
  toFun z := cross2 v z
  map_add' := cross2_add_right v
  map_smul' a z := cross2_smul_right v z a

theorem coordinateLinear_ne_zero : coordinateLinear≠0 := by
  intro h
  have hh := congrArg (fun f : Plane →ₗ[ℝ] ℝ => f (EuclideanSpace.single 0 1)) h
  change (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) 0=0 at hh
  simp at hh

theorem crossLinear_ne_zero (v : Plane) (hv : ‖v‖=1) : crossLinear v≠0 := by
  intro h
  have h0 := congrArg (fun f : Plane →ₗ[ℝ] ℝ => f (EuclideanSpace.single 0 1)) h
  have h1 := congrArg (fun f : Plane →ₗ[ℝ] ℝ => f (EuclideanSpace.single 1 1)) h
  have he0 : v 0=0 := by simpa [crossLinear,cross2] using h1
  have he1 : v 1=0 := by simpa [crossLinear,cross2] using h0
  have hz : v=0 := by
    ext i
    fin_cases i
    · exact he0
    · exact he1
  rw [hz,norm_zero] at hv
  norm_num at hv

def PennyGraph.coverForm {n : ℕ} (G : PennyGraph n) : Fin n ⊕ OrientedEdge G → Plane →ₗ[ℝ] ℝ
  | .inl _ => coordinateLinear
  | .inr e => crossLinear (carriedVector e)

def PennyGraph.coverLevel {n : ℕ} (G : PennyGraph n) : Fin n ⊕ OrientedEdge G → ℝ
  | .inl i => coordinateLinear (G.point i)
  | .inr e => crossLinear (carriedVector e) (G.point e.val.1)

theorem PennyGraph.coverForm_ne_zero {n : ℕ} (G : PennyGraph n) (i : Fin n ⊕ OrientedEdge G) :
    G.coverForm i≠0 := by
  cases i with
  | inl i => exact coordinateLinear_ne_zero
  | inr e => exact crossLinear_ne_zero _ (carriedVector_norm e)

theorem PennyGraph.drawing_affine_cover {n : ℕ} (G : PennyGraph n) :
    ∀ z∈G.drawing, ∃ i, G.coverForm i z=G.coverLevel i := by
  intro z hz
  rcases hz with ⟨i,rfl⟩ | he
  · exact ⟨.inl i,rfl⟩
  · obtain ⟨e,he⟩ := Set.mem_iUnion.mp he
    obtain ⟨t,_,rfl⟩ := he
    refine ⟨.inr e,?_⟩
    change cross2 (carriedVector e) (G.edgePoint e.val.1 e.val.2 t)=
      cross2 (carriedVector e) (G.point e.val.1)
    apply sub_eq_zero.mp
    rw [← cross2_sub_right]
    have hd : G.edgePoint e.val.1 e.val.2 t-G.point e.val.1=t • carriedVector e := by
      dsimp [PennyGraph.edgePoint,carriedVector]
      module
    rw [hd,cross2_smul_right,cross2_self,mul_zero]

instance planeFaceFinite {n : ℕ} (G : PennyGraph n) : Finite (PlaneFace G) :=
  finite_faces_of_affine_cover G G.coverForm G.coverLevel G.coverForm_ne_zero G.drawing_affine_cover

instance boundedFaceFinite {n : ℕ} (G : PennyGraph n) : Finite (BoundedFace G) :=
  Finite.of_injective (fun F : BoundedFace G => (⟨F.val,F.property.1⟩ : PlaneFace G))
    (fun _ _ h => Subtype.ext (congrArg (fun F : PlaneFace G => F.val) h))

noncomputable instance {n : ℕ} (G : PennyGraph n) : Fintype (BoundedFace G) := Fintype.ofFinite _

end Swanepoel
