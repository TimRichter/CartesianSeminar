> module CoinductiveCalculus.CoinductiveCalculus

> import Syntax.PreorderReasoning

> %default total
> %access public export
> %auto_implicits off

> %hide Stream
> %hide head
> %hide tail
> %hide (+)
> %hide plusZeroRightNeutral


* Streams

For a type |T|, streams of values of type |T| can be described by values
of type |Stream T| with

> Stream : Type -> Type

The idea is that any |Stream T| has a head and a tail

> head : {T : Type} -> Stream T -> T
> tail : {T : Type} -> Stream T -> Stream T

and that piecing together a |T| with a |Stream T| yields a |Stream T|:

> cons : {T : Type} -> T -> Stream T -> Stream T

The stream operations |head|, |tail| and |cons| are required to fulfil
three properties:

> headConsProp : {T : Type} -> (t : T) -> (s : Stream T) -> head (cons t s) = t  

> tailConsProp : {T : Type} -> (t : T) -> (s : Stream T) -> tail (cons t s) = s

> consHeadTailProp : {T : Type} -> (s : Stream T) -> cons (head s) (tail s) = s 


* Differentiation and integration

We want to look at differentiation and integration of functions of real
variables from the point of view of streams. More specifically, we want
to understand which properties differentiation and integration have to
fulfill when we consider these operations as operations on streams of
type |Stream R = R -> R|. Here

> R : Type

is meant to represent real numbers and

> F : Type
> F = R -> R

are differentiable and integrable functions on |R|. For the time being,
we represent differentiation and integration through functions

> D : F -> F
> S : R -> R -> F -> R

with |D f| and |S a b f| representing the derivative of |f| and the
integral of |f| on |[a,b]|. 


* Head, tail and cons for functions/streams

How can we implement |head| for |Stream R = F|? We have

> headF : F -> R

The natural way to compute a real number from a |f : F| is to simply
evaluate |f|. We require our "real numbers" to contain a zero element

> zero : R

and we define

> headF f = f zero

What about the tail of a function |f|?

> tailF : F -> F

The type of |tailF| is |F -> F|, just like the type of |D|. Thus, we
take

> tailF = D

We are left with the implementation of |consF|:

> consF : R -> F -> F

Of course, we want |headF|, |tailF| and |consF| to fulfill the
properties of stream operations. In particular, we want

< consF (headF f) (tailF f) = f

For |f = consF a g| and our definitions of |headF| and |tailF|, this is
equivalent to

< consF (headF f) (tailF f) = f
<
<   ={ def. of f }=
<
< consF (headF (consF a g)) (tailF (consF a g)) = consF a g
<
<   ={ def. of consF, tailF }=
<
< consF ((consF a g) zero) (D (consF a g)) = consF a g

Sufficient conditions for the last equality to hold are

< (consF a g) zero = a 

and 

< D (consF a g) = g

The first condition could be fulfilled by defining |consF a g| to be
|const a|. But the second condition requires |consF a g| has to be an
anti-derivative of |g|. This suggests the definition

> (+) : R -> R -> R

> consF a f = \ x => a + S zero x f

where we can think of |(+)| as representing the standard addition on
real numbers.


* Properties of |R|, |D| and |S|

Which properties do |R|, |D| and |S| have to satisfy for |headF|,
|tailF| and |consF| to be stream operations? Our definition already
requires |R| to be equipped with a zero element and with a |(+)|:

< R : Type
< zero : R
< (+) : R -> R -> R

If we also require integration to fulfill

> intProp1 : (a : R) -> (f : F) -> S a a f = zero

and |zero| to be a

> plusZeroRightNeutral : (left : R) -> left + zero = left 

We can derive a formal proof of |headF (consF a f) = a|:

> headConsPropF : (a : R) -> (f : F) -> headF (consF a f) = a  
> headConsPropF a f = ( headF (consF a f) )
>                   ={ Refl }=
>                     ( headF (\ x => a + S zero x f) )
>                   ={ Refl }=
>                     ( a + S zero zero f )
>                   ={ cong (intProp1 zero f) }=  
>                     ( a + zero )
>                   ={ plusZeroRightNeutral a }=
>                     ( a )
>                   QED

Satisfying |tailF (consF a f) = f| requires some more assumptions.
Consistently with the interpretation of |D f| representing the
derivative of |f|, we need

> derConstZero : (a : R) -> D (const a) = const zero

and

> derLinear1 : (f, g : F) -> D (\ x => f x + g x) = \ x => (D f) x + (D g) x

Moreover |S| has to be an "anti-derivative"

> intAntiDer : (f : F) -> D (\ x => S zero x f) = f

We also need |zero| to be left-neutral

> plusZeroLeftNeutral : (right : R) -> zero + right = right 

and equality on |F| to be extensional:

> extEqF : (f, g : F) -> ((x : R) -> f x = g x) -> f = g

With these assumptions, we can derive

> lemma : (f : F) -> (x : R) -> zero + f x = f x
> lemma f x = ( zero + f x )
>           ={ plusZeroLeftNeutral (f x) }=
>             ( f x )
>           QED

and, finally

> tailConsPropF : (a : R) -> (f : F) -> tailF (consF a f) = f  
> tailConsPropF a f = ( tailF (consF a f) )
>                   ={ Refl }=
>                     ( tailF (\ x => a + S zero x f) )
>                   ={ Refl }=
>                     ( D (\ x => a + S zero x f) ) 
>                   ={ Refl }=
>                     ( D (\ x => (const a) x + (\ y => S zero y f) x) )  
>                   ={ derLinear1 (const a) (\ y => S zero y f) }=
>                     ( \ x => (D (const a)) x + (D (\ y => S zero y f)) x ) 
>                   ={ cong {f = \ h => \ x => h x + (D (\ y => S zero y f)) x } (derConstZero a) }=
>                     ( \ x => (const zero) x + (D (\ y => S zero y f)) x )
>                   ={ cong {f = \ h => \ x => (const zero) x + h x} (intAntiDer f) }=
>                     ( \ x => (const zero) x + f x )
>                   ={ Refl }=
>                     ( \ x => zero + f x )
>                   ={ extEqF (\ x => zero + f x) (\ x => f x) (lemma f) }=
>                     ( \ x => f x )
>                   ={ Refl }=  
>                     ( f )
>                   QED

We are left with the last property: |consF (headF f) (tailF f) = f|. To
prove this property, we need three more assumptions

> (-) : R -> R -> R

> plusAnyMinus : (x, y : R) -> x + (y - x) = y

> derAntiInt : (f : F) -> (a : R) -> (b : R) -> S a b (D f) = f b - f a

With these, one has

> lemma1 : (c : R) -> (f : F) -> (x : R) -> (c + (f x - c) = f x)
> lemma1 c f x = plusAnyMinus c (f x)

> lemma2 : (f : F) -> (c : R) -> (a : R) -> (b : R) -> c + S a b (D f) = c + (f b - f a)
> lemma2 f c a b = ( c + S a b (D f) )
>                ={ cong (derAntiInt f a b) }=
>                  ( c + (f b - f a) )
>                QED

> consHeadTailPropF : (f : F) -> consF (headF f) (tailF f) = f 
> consHeadTailPropF f = ( consF (headF f) (tailF f) )
>                     ={ Refl }=
>                       ( consF (f zero) (D f) )
>                     ={ Refl }=
>                       ( \ x => f zero + S zero x (D f) )
>                     ={ extEqF (\ x => f zero + S zero x (D f))
>                               (\ x => f zero + (f x - f zero))
>                               (lemma2 f (f zero) zero) }=
>                       ( \ x => f zero + (f x - f zero) )
>                     ={ extEqF (\ x => f zero + (f x - f zero)) 
>                               (\ x => f x) 
>                               (lemma1 (f zero) f) }=
>                       ( \ x => f x )  
>                     ={ Refl }=
>                       ( f )
>                     QED


* Properties of |R|, |D| and |S| (wrap up)

  ( 1) R : Type
  ( 2) zero : R
  ( 3) (+)  :  R -> R -> R
  ( 4) (-)  :  R -> R -> R
  ( 5) plusAnyMinus : (x, y : R) -> x + (y - x) = y
  ( 6) plusZeroLeftNeutral   :  (right : R) -> zero + right = right 
  ( 7) plusZeroRightNeutral  :  ( left : R) -> left +  zero =  left 

  ( 8) derConstZero : (a : R) -> D (const a) = const zero
  ( 9) derLinear1 : (f, g : F) -> D (\ x => f x + g x) = \ x => (D f) x + (D g) x

  (10) intProp1 : (a : R) -> (f : F) -> S a a f = zero
  (11) intAntiDer : (f : F) -> D (\ x => S zero x f) = f
  (12) derAntiInt : (f : F) -> (a : R) -> (b : R) -> S a b (D f) = f b - f a

  (13) extEqF : (f, g : F) -> ((x : R) -> f x = g x) -> f = g


Properties (1-7) follow from standard axioms on real numbers. (8-9)
follow from the standard definition of derivative. (10-12) follows from ?
  
  

> {-

> ---}
 
