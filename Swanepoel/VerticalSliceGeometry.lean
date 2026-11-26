module
public import Swanepoel.FaceBoundaryOrder
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def cartPoint (x y : ℝ) : Plane := WithLp.toLp 2 ![x,y]

@[simp] theorem cartPoint_zero (x y : ℝ) : cartPoint x y 0=x := rfl
@[simp] theorem cartPoint_one (x y : ℝ) : cartPoint x y 1=y := rfl

theorem continuous_cartPoint (x : ℝ) : Continuous (cartPoint x) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_const
  · exact continuous_id

theorem cartPoint_dist (x y z : ℝ) : dist (cartPoint x y) (cartPoint x z)=|y-z| := by
  have h : cartPoint x y-cartPoint x z=(y-z) • EuclideanSpace.single (1:Fin 2) (1:ℝ) := by
    ext i
    fin_cases i <;> simp [cartPoint]
  have hn : ‖EuclideanSpace.single (1:Fin 2) (1:ℝ)‖=1 := by
    have hh : ‖EuclideanSpace.single (1:Fin 2) (1:ℝ)‖^2=1 := by
      simp
    nlinarith only [hh,norm_nonneg (EuclideanSpace.single (1:Fin 2) (1:ℝ))]
  rw [dist_eq_norm,h,norm_smul,hn,Real.norm_eq_abs,mul_one]

def PennyGraph.sliceEdges {n : ℕ} (G : PennyGraph n) (x : ℝ) : Finset (ContactEdge G) :=
  Finset.univ.filter (fun e => min (G.point e.val.1 0) (G.point e.val.2 0)<x ∧
    x<max (G.point e.val.1 0) (G.point e.val.2 0))

abbrev SliceEdge {n : ℕ} (G : PennyGraph n) (x : ℝ) := {e : ContactEdge G // e∈G.sliceEdges x}

noncomputable instance {n : ℕ} (G : PennyGraph n) (x : ℝ) : Fintype (SliceEdge G x) :=
  Fintype.ofFinite _

def ContactEdge.sliceParameter {n : ℕ} {G : PennyGraph n} (e : ContactEdge G) (x : ℝ) : ℝ :=
  (x-G.point e.val.1 0)/(G.point e.val.2 0-G.point e.val.1 0)

def ContactEdge.sliceHeight {n : ℕ} {G : PennyGraph n} (e : ContactEdge G) (x : ℝ) : ℝ :=
  G.point e.val.1 1+e.sliceParameter x*(G.point e.val.2 1-G.point e.val.1 1)

theorem parameter_of_strict_between {a b x : ℝ} (h : min a b<x ∧ x<max a b) :
    b-a≠0 ∧ 0<(x-a)/(b-a) ∧ (x-a)/(b-a)<1 := by
  rcases lt_trichotomy a b with hab | hab | hab
  · rw [min_eq_left hab.le,max_eq_right hab.le] at h
    have hd : 0<b-a := sub_pos.mpr hab
    exact ⟨ne_of_gt hd,div_pos (sub_pos.mpr h.1) hd,
      (div_lt_iff₀ hd).mpr (by linarith only [h.2])⟩
  · subst b
    simp only [min_self,max_self] at h
    exact False.elim (lt_asymm h.1 h.2)
  · rw [min_eq_right hab.le,max_eq_left hab.le] at h
    have hd : b-a<0 := sub_neg.mpr hab
    exact ⟨ne_of_lt hd,div_pos_of_neg_of_neg (sub_neg.mpr h.2) hd,
      (div_lt_iff_of_neg hd).mpr (by linarith only [h.1])⟩

theorem ContactEdge.sliceParameter_bounds {n : ℕ} {G : PennyGraph n} (e : ContactEdge G)
    {x : ℝ} (he : e∈G.sliceEdges x) :
    G.point e.val.2 0-G.point e.val.1 0≠0 ∧ 0<e.sliceParameter x ∧ e.sliceParameter x<1 :=
  parameter_of_strict_between (Finset.mem_filter.mp he).2

theorem ContactEdge.edgePoint_slice {n : ℕ} {G : PennyGraph n} (e : ContactEdge G)
    {x : ℝ} (he : e∈G.sliceEdges x) :
    G.edgePoint e.val.1 e.val.2 (e.sliceParameter x)=cartPoint x (e.sliceHeight x) := by
  have h := div_mul_cancel₀ (x-G.point e.val.1 0) (e.sliceParameter_bounds he).1
  change e.sliceParameter x*(G.point e.val.2 0-G.point e.val.1 0)=x-G.point e.val.1 0 at h
  ext i
  fin_cases i
  · change (1-e.sliceParameter x)*G.point e.val.1 0+e.sliceParameter x*G.point e.val.2 0=x
    linarith only [h]
  · change (1-e.sliceParameter x)*G.point e.val.1 1+e.sliceParameter x*G.point e.val.2 1=
      G.point e.val.1 1+e.sliceParameter x*(G.point e.val.2 1-G.point e.val.1 1)
    ring

theorem PennyGraph.sliceHeight_injective {n : ℕ} (G : PennyGraph n) (x : ℝ) :
    Function.Injective (fun e : SliceEdge G x => e.val.sliceHeight x) := by
  intro e f hef
  change e.val.sliceHeight x=f.val.sliceHeight x at hef
  have he := e.val.sliceParameter_bounds e.property
  have hf := f.val.sliceParameter_bounds f.property
  have hp : G.edgePoint e.val.val.1 e.val.val.2 (e.val.sliceParameter x)=
      G.edgePoint f.val.val.1 f.val.val.2 (f.val.sliceParameter x) := by
    rw [e.val.edgePoint_slice e.property,f.val.edgePoint_slice f.property,hef]
  exact Subtype.ext (e.val.eq_of_unordered_eq f.val
    (G.interior_edge_intersection _ _ _ _ e.val.property.2 f.val.property.2 he.2.1 he.2.2 hf.2.1.le hf.2.2.le hp))

theorem PennyGraph.cartPoint_mem_drawing_iff {n : ℕ} (G : PennyGraph n)
    (x : ℝ) (hx : ∀ v : Fin n,x≠G.point v 0) (y : ℝ) :
    cartPoint x y∈G.drawing ↔ ∃ e : SliceEdge G x,y=e.val.sliceHeight x := by
  constructor
  · intro hdraw
    rw [← G.subdrawing_univ] at hdraw
    rcases hdraw with ⟨v,hv⟩ | hdraw
    · exact False.elim (hx v (congrArg (fun z : Plane => z 0) hv).symm)
    obtain ⟨e,he⟩ := Set.mem_iUnion.mp hdraw
    obtain ⟨_,t,⟨ht0,ht1⟩,hpoint⟩ := Set.mem_iUnion.mp he
    have hcoord := congrArg (fun z : Plane => z 0) hpoint
    change (1-t)*G.point e.val.1 0+t*G.point e.val.2 0=x at hcoord
    have ht0' : 0<t := by
      by_contra hn
      have ht : t=0 := le_antisymm (le_of_not_gt hn) ht0
      apply hx e.val.1
      simpa only [ht,sub_zero,one_mul,zero_mul,add_zero] using hcoord.symm
    have ht1' : t<1 := by
      by_contra hn
      have ht : t=1 := le_antisymm ht1 (le_of_not_gt hn)
      apply hx e.val.2
      simpa only [ht,sub_self,zero_mul,one_mul,zero_add] using hcoord.symm
    have hbetween : min (G.point e.val.1 0) (G.point e.val.2 0)<x ∧
        x<max (G.point e.val.1 0) (G.point e.val.2 0) := by
      rcases lt_trichotomy (G.point e.val.1 0) (G.point e.val.2 0) with h | h | h
      · rw [min_eq_left h.le,max_eq_right h.le]
        constructor <;> nlinarith only [hcoord,ht0',ht1',h]
      · exact False.elim (hx e.val.1 (by rw [← h] at hcoord; linarith only [hcoord]))
      · rw [min_eq_right h.le,max_eq_left h.le]
        constructor <;> nlinarith only [hcoord,ht0',ht1',h]
    have heSlice : e∈G.sliceEdges x := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hbetween⟩
    have hparam : t=e.sliceParameter x := by
      apply (eq_div_iff (e.sliceParameter_bounds heSlice).1).mpr
      linarith only [hcoord]
    refine ⟨⟨e,heSlice⟩,?_⟩
    have hpoint' := e.edgePoint_slice heSlice
    rw [← hparam,hpoint] at hpoint'
    exact congrArg (fun z : Plane => z 1) hpoint'
  · rintro ⟨e,rfl⟩
    have he := e.val.sliceParameter_bounds e.property
    apply G.edgeTrace_subset_drawing _ _ e.val.property.2
    exact ⟨e.val.sliceParameter x,⟨he.2.1.le,he.2.2.le⟩,e.val.edgePoint_slice e.property⟩

theorem ContactEdge.slice_cross_difference {n : ℕ} {G : PennyGraph n} (e : ContactEdge G)
    (x y : ℝ) :
    cross2 (carriedVector e.forwardEdge) (cartPoint x y)-
      cross2 (carriedVector e.forwardEdge) (cartPoint x (e.sliceHeight x))=
        (G.point e.val.2 0-G.point e.val.1 0)*(y-e.sliceHeight x) := by
  simp [cross2,carriedVector,ContactEdge.forwardEdge,cartPoint]
  ring

end Swanepoel
