import Algae.Group

class Cat.{u, v} where
  obj: Type u
  hom: obj → obj → Type v
  id {a: obj}: hom a a
  comp {a b c: obj}: hom a b → hom b c → hom a c
  id_left {a b: obj} (f: hom a b): comp id f = f
  id_right {a b: obj} (f: hom a b): comp f id = f
  associative {a b c d: obj} (f: hom a b) (g: hom b c) (h: hom c d):
    comp (comp f g) h = comp f (comp g h)

namespace Cat

variable {α: Type u}

-- Notation is too complex to use.

-- infixr:10 " ⟶ " => Cat.hom
-- infixr:70 " ; " => Cat.comp

-- instance [C: Cat] (x: C.obj): OfNat (x ⟶ x) 1 := {
--   ofNat := Cat.id
-- }

-- The category of types.
def Sets: Cat.{u + 1} := {
  obj := Type u
  hom := λ x y ↦ x → y
  id := Function.id
  comp := λ f g ↦ g ∘ f
  id_left := by intros; rfl
  id_right := by intros; rfl
  associative := by intros; rfl
}

-- Turn a monoid into a one-object category.
def Monoid.toCat {α: Type u} (M: Monoid α): Cat := {
  obj := Unit
  hom := λ _ _ ↦ α
  id := 0
  comp := M.op
  id_left := M.identity.left
  id_right := M.identity.right
  associative := M.assoc
}

-- The monoid of endomorphisms on an object.
def Cat.endomonoid {C: Cat} (x: obj): Monoid (hom x x) := {
  op := C.comp
  unit := id
  identity := ⟨C.id_left, C.id_right⟩
  assoc := C.associative
}

def opposite (C: Cat): Cat := {
  obj := obj
  hom := λ x y ↦ hom y x
  id := id
  comp := λ f g ↦ comp g f
  id_left := C.id_right
  id_right := C.id_left
  associative := λ f g h => Eq.symm (C.associative h g f)
}

def IsMono {C: Cat} {x y: obj} (f: hom x y): Prop :=
  ∀ w, ∀ e₁ e₂: hom w x, comp e₁ f = comp e₂ f → e₁ = e₂

def IsMono.id {C: Cat} (x: obj): IsMono (@C.id x) := by
  intro w e₁ e₂ h
  rw [←C.id_right e₁, ←C.id_right e₂]
  exact h

def IsMono.comp {C: Cat} {x y z: obj} {f: hom x y} {g: hom y z}
  (hf: IsMono f) (hg: IsMono g): IsMono (comp f g) := by
  intro _ _ _ h
  apply hf; apply hg
  repeat rw [C.associative, C.associative, h]

def IsEpi {C: Cat} {x y: obj} (f: hom x y): Prop :=
  @IsMono C.opposite _ _ f

def IsEpi.id {C: Cat} (x: obj): IsEpi (@C.id x) := by
  apply IsMono.id

def IsEpi.comp {C: Cat} {x y z: obj} {f: hom x y} {g: hom y z}
  (hf: IsEpi f) (hg: IsEpi g): IsEpi (C.comp f g) := by
  apply IsMono.comp hg hf

def Inverses {C: Cat} {x y: obj} (f: hom x y) (g: hom y x): Prop :=
  comp f g = id

theorem Inverses.id {C: Cat} (x: obj): Inverses (@C.id x) (@C.id x) := by
  apply C.id_left

theorem Inverses.comp {C: Cat} {x y z: obj} {f₁: hom x y} {f₂: hom y z}
  {g₁: hom y x} {g₂: hom z y} (h₁: Inverses f₁ g₁) (h₂: Inverses f₂ g₂):
  Inverses (C.comp f₁ f₂) (C.comp g₂ g₁) := by
  rw [Inverses, C.associative, ←C.associative f₂, h₂, C.id_left g₁, h₁]

def IsoPair {C: Cat} {x y: obj} (f: hom x y) (g: hom y x): Prop :=
  Inverses f g ∧ Inverses g f

def IsoPair.id {C: Cat} {x: obj}: IsoPair (@C.id x) (@C.id x) := by
  constructor; repeat apply Inverses.id

def IsoPair.symm {C: Cat} {x y: obj} {f: hom x y} {g: hom y x} (h: IsoPair f g): IsoPair g f := by
  exact And.symm h

def IsoPair.comp {C: Cat} {x y z: obj} {f₁: hom x y} {f₂: hom y z}
  {g₁: hom y x} {g₂: hom z y} (h₁: IsoPair f₁ g₁) (h₂: IsoPair f₂ g₂): IsoPair (C.comp f₁ f₂) (C.comp g₂ g₁) := by
  constructor
  exact Inverses.comp h₁.1 h₂.1
  exact Inverses.comp h₂.2 h₁.2

def IsIso {C: Cat} {x y: obj} (f: hom x y): Prop :=
  ∃ g, IsoPair f g

theorem IsIso.id {C: Cat} {x: obj}: IsIso (@C.id x) := by
  exists C.id
  exact IsoPair.id

theorem IsIso.comp {C: Cat} {x y z: obj} {f₁: hom x y} {f₂: hom y z}
  (h₁: IsIso f₁) (h₂: IsIso f₂): IsIso (C.comp f₁ f₂) := by
  obtain ⟨g₁, h₁⟩ := h₁
  obtain ⟨g₂, h₂⟩ := h₂
  exists C.comp g₂ g₁
  exact IsoPair.comp h₁ h₂

theorem IsoPair.isIso_left {C: Cat} {x y: obj} {f: hom x y} {g: hom y x} (h: IsoPair f g): IsIso f := by
  exists g

theorem IsoPair.isIso_right {C: Cat} {x y: obj} {f: hom x y} {g: hom y x} (h: IsoPair f g): IsIso g := by
  exists f
  exact IsoPair.symm h

def mono {C: Cat.{u, v}} (x y: obj): Type v :=
  Subtype (fun f: hom x y ↦ IsMono f)

def epi {C: Cat.{u, v}} (x y: obj): Type v :=
  Subtype (fun f: hom x y ↦ IsMono f)

def iso {C: Cat.{u, v}} (x y: obj): Type v :=
  Subtype (fun f: hom x y ↦ IsIso f)

-- The automorphism group on an object.
-- noncomputable def autogroup {C: Cat} (x: C.obj): Group (iso x x) := {
--   op := λ f g ↦ ⟨comp f.val g.val, IsIso.comp f.property g.property⟩
--   point := ⟨id, IsIso.id⟩
--   identity := by
--     constructor
--     intro f
--     simp
--     congr
--     sorry
--     sorry
--   associative := by
--     intro f g h
--     simp
--     sorry
--   inv := λ f ↦ ⟨f.property.choose, IsoPair.isIso_right f.property.choose_spec⟩
--   inverse := by
--     constructor <;> (intro f; simp; congr)
--     exact f.property.choose_spec.right
--     exact f.property.choose_spec.left
-- }


theorem mono_if {C: Cat} {x y: obj} {f: hom x y} (g: hom y x) (h: comp f g = id): IsMono f := by
  intro _ e₁ e₂ h₂
  rw [←C.id_right e₁, ←h, ←C.associative, h₂, C.associative, h, C.id_right]

theorem epi_if {C: Cat} {x y: obj} {f: hom x y} (g: hom y x) (h: comp g f = id): IsEpi f := by
  exact mono_if _ h


theorem set_mono {x y: Sets.obj} {f: Sets.hom x y}: IsMono f ↔ Function.Injective f := by
  sorry

theorem set_epi {x y: Sets.obj} {f: Sets.hom x y}: IsEpi f ↔ Function.Surjective f := by
  sorry

def Product (C D: Cat): Cat := {
  obj := C.obj × D.obj
  hom := λ x y ↦ C.hom x.1 y.1 × D.hom x.2 y.2
  id := ⟨C.id, D.id⟩
  comp := λ f g ↦ ⟨C.comp f.1 g.1, D.comp f.2 g.2⟩
  id_left := by intros; ext; apply C.id_left; apply D.id_left
  id_right := by intros; ext; apply C.id_right; apply D.id_right
  associative := by intros; ext; apply C.associative; apply D.associative
}

structure Functor (C D: Cat) where
  obj: C.obj → D.obj
  hom {x y: C.obj}: (C.hom x y) → D.hom (obj x) (obj y)
  id_preserve: ∀ x, hom (C.id) = @D.id (obj x)
  comp_preserve: ∀ x y z, ∀ f: C.hom x y, ∀ g: C.hom y z,
    hom (C.comp f g) = D.comp (hom f) (hom g)

def Functor.id {C: Cat}: Functor C C := {
  obj := λ x ↦ x
  hom := λ f ↦ f
  id_preserve := by intros; rfl
  comp_preserve := by intros; rfl
}

def Functor.comp {C D E: Cat} (F: Functor C D) (G: Functor D E): Functor C E := {
  obj := G.obj ∘ F.obj
  hom := G.hom ∘ F.hom
  id_preserve := by simp [F.id_preserve, G.id_preserve]
  comp_preserve := by simp [F.comp_preserve, G.comp_preserve]
}

-- ?
def Powerset (X: Type u): Type u :=
  X → Prop

-- Set the category of sets
-- X: Type u
-- Powerset(X): Type u
-- endofunction f: X → X
-- Powerset: (Type u) → (Type u)
-- okay
example : Functor Sets.{u} Sets.{u} := {
  obj := Powerset
  hom := Set.image
  id_preserve := sorry
  comp_preserve := sorry
}

-- (u+1)-Cat of u-Categories
example: Cat.{u + 1} := {
  obj := Cat.{u}
  hom := Functor
  id := @Functor.id
  comp := Functor.comp
  id_left := by intros; rfl
  id_right := by intros; rfl
  associative := by intros; rfl
}

-- natural transformation bewteen functors
structure NatTrans {C D: Cat} (F G: Functor C D) where
  component (x: C.obj): hom (F.obj x) (G.obj x)
  commute: ∀ {x y} f,
    D.comp (F.hom f) (component y) = D.comp (component x) (G.hom f)

def NatTrans.id {C D: Cat} {F: Functor C D}: NatTrans F F := {
  component := λ _ ↦ D.id
  commute := by
    intros
    repeat rw [←F.id_preserve, ←F.comp_preserve]
    rw [C.id_right, C.id_left]
}

def NatTrans.comp {C D: Cat} {F G H: Functor C D}
  (η: NatTrans F G) (ε: NatTrans G H): NatTrans F H := {
  component := λ x ↦ D.comp (η.component x) (ε.component x)
  commute := by
    intros
    rw [←D.associative, η.commute, D.associative, ε.commute, ←D.associative]
  }

def FunctorCat (C D: Cat): Cat := {
  obj := Functor C D
  hom := NatTrans
  id := NatTrans.id
  comp := NatTrans.comp
  id_left := by
    intros; simp [NatTrans.comp]
    congr; ext; apply D.id_left
  id_right := by
    intros; simp [NatTrans.comp]
    congr; ext; apply D.id_right
  associative := by
    intros; simp [NatTrans.comp]
    ext; apply D.associative
}

def NatIso {C D: Cat} {F G: Functor C D} (η: NatTrans F G): Prop :=
  @IsIso (FunctorCat C D) F G η

-- https://proofwiki.org/wiki/Equivalence_of_Definitions_of_Natural_Isomorphism_between_Covariant_Functors
theorem NatTrans.iso_iff {C D: Cat} {F G: Functor C D} {η: NatTrans F G}: NatIso η ↔ ∀ x, IsIso (η.component x) := by
  sorry

class PreGroupoid extends Cat where
  inv {x y: obj}: (hom x y) → (hom y x)

postfix:max "⁻¹" => PreGroupoid.inv

class Groupoid extends PreGroupoid where
  inv_left {x y: obj} (f: hom x y):
    comp f⁻¹ f = id
  inv_right {x y: obj} (f: hom x y):
    comp f f⁻¹ = id

noncomputable def Groupoid.autogroup {C: Groupoid} (x: obj): Group (hom x x) := {
  op := C.comp
  unit := id
  identity := ⟨C.id_left, C.id_right⟩
  assoc := C.associative
  inv := C.inv
  inverse := ⟨C.inv_left, C.inv_right⟩
}
