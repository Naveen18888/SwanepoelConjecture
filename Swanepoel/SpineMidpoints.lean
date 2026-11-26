module
public import Swanepoel.SpineCones
public import Mathlib.Tactic.Module
@[expose] public section

noncomputable section
namespace Swanepoel

def stepCenter {n : ℕ} {G : PennyGraph n} (e f : OrientedEdge G) : Plane :=
  RhombusCell.midpoint2 (edgeCenter e) (edgeCenter f)

theorem stepCenter_comm {n : ℕ} {G : PennyGraph n} (e f : OrientedEdge G) :
    stepCenter e f=stepCenter f e := by
  unfold stepCenter RhombusCell.midpoint2
  rw [add_comm]

theorem edgeCenter_reverse {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) :
    edgeCenter (reverseEdge e)=edgeCenter e := by
  unfold edgeCenter reverseEdge RhombusCell.midpoint2
  simp only
  rw [add_comm]

theorem stepCenter_reverse {n : ℕ} {G : PennyGraph n} (e f : OrientedEdge G) :
    stepCenter (reverseEdge e) (reverseEdge f)=stepCenter e f := by
  simp only [stepCenter,edgeCenter_reverse]

theorem step_centers_forward_cone {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {e f g k : OrientedEdge G} (hef : PositiveCellStep e f) (hgk : PositiveCellStep g k)
    (hfg : Relation.ReflTransGen PositiveCellStep f g) :
    SpineCone (carriedVector e) (stepCenter g k-stepCenter e f) := by
  have hv1 := hef.to_cellStep.vector_eq
  have hv2 : carriedVector e=carriedVector g := hv1.trans (positive_path_vector hfg)
  have h1 := (hef.displacement_cone ht).smul (by norm_num : (0 : ℝ) < 1/2)
  have h2 := positive_path_cone ht hfg
  rw [← hv1] at h2
  have h3 := (hgk.displacement_cone ht).smul (by norm_num : (0 : ℝ) < 1/2)
  rw [← hv2] at h3
  have hsum := (h1.add_weak h2).add h3
  have heq : (1/2 : ℝ) • (edgeCenter f-edgeCenter e)+(edgeCenter g-edgeCenter f)+
      (1/2 : ℝ) • (edgeCenter k-edgeCenter g)=stepCenter g k-stepCenter e f := by
    unfold stepCenter RhombusCell.midpoint2
    module
  rwa [heq] at hsum

theorem ordered_step_centers {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {e f g k : OrientedEdge G} (hef : PositiveCellStep e f) (hgk : PositiveCellStep g k)
    (heg : Relation.ReflTransGen PositiveCellStep e g) :
    (e=g ∧ f=k) ∨ SharpNormal (carriedVector e) (stepCenter g k-stepCenter e f) := by
  rcases heg.cases_head with h | ⟨p,hep,hpg⟩
  · subst g
    exact Or.inl ⟨rfl,positive_step_functional ht hef hgk⟩
  · have hp := positive_step_functional ht hef hep
    subst p
    exact Or.inr ((step_centers_forward_cone ht hef hgk hpg).sharpNormal (carriedVector_norm e))

theorem aligned_step_centers {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {s e f g k : OrientedEdge G} (hse : Relation.ReflTransGen PositiveCellStep s e)
    (hsg : Relation.ReflTransGen PositiveCellStep s g)
    (hef : PositiveCellStep e f) (hgk : PositiveCellStep g k) :
    (e=g ∧ f=k) ∨ SharpNormal (carriedVector e) (stepCenter g k-stepCenter e f) := by
  have huniq : Relator.RightUnique (PositiveCellStep (G := G)) := by
    intro a b c h1 h2
    exact positive_step_functional ht h1 h2
  have hcomp := Relation.ReflTransGen.total_of_right_unique huniq hse hsg
  rcases hcomp with h | h
  · exact ordered_step_centers ht hef hgk h
  · rcases ordered_step_centers ht hgk hef h with hh | hh
    · exact Or.inl ⟨hh.1.symm,hh.2.symm⟩
    · have hv : carriedVector e=carriedVector g :=
        (positive_path_vector hse).symm.trans (positive_path_vector hsg)
      rw [← hv] at hh
      have hneg : stepCenter e f-stepCenter g k= -(stepCenter g k-stepCenter e f) := by abel
      rw [hneg] at hh
      exact Or.inr ((SharpNormal.neg_iff _ _).mp hh)

theorem component_step_centers {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {e f g k : OrientedEdge G} (hef : PositiveCellStep e f) (hgk : PositiveCellStep g k)
    (hq : edgeComponent e=edgeComponent g) :
    (e=g ∧ f=k) ∨ (e=reverseEdge k ∧ f=reverseEdge g) ∨
      SharpNormal (carriedVector e) (stepCenter g k-stepCenter e f) := by
  obtain ⟨s,t,hs,htop,he,hall⟩ := component_spine_iff ht e
  have hg := (hall g).mp hq.symm
  rcases hg with hg | hg
  · rcases aligned_step_centers ht he.1 hg.1 hef hgk with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · have hnrev : ¬ ∃ z, PositiveCellStep (reverseEdge s) z := by
      rintro ⟨z,hz⟩
      have hh := hz.reverse
      simp only [reverseEdge_involutive] at hh
      exact hs ⟨reverseEdge z,hh⟩
    have hkt := spine_suffix_closed ht hnrev hg.2 hgk
    have hsrk : Relation.ReflTransGen PositiveCellStep s (reverseEdge k) := by
      simpa only [reverseEdge_involutive] using positive_path_reverse hkt
    rcases aligned_step_centers ht he.1 hsrk hef hgk.reverse with h | h
    · exact Or.inr (Or.inl h)
    · rw [stepCenter_reverse,stepCenter_comm k g] at h
      exact Or.inr (Or.inr h)

end Swanepoel
