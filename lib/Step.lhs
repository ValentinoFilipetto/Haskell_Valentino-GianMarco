\subsection{The step rule}
The step rule is what allows us to develop our tableau in that it tells us what to do based on what we have inside the lists of a specific node. However, it is very long and cumbersome, so we only explain the most important parts of it.

As we have seen, a node is composed of six lists, and the step rule is essentially divided into three parts accordingly: the first acts on the list of pending formulas that don’t lead to any deletion of $F$ formulas (i), the second one on the list of pending formulas with the shape $F(\neg \varphi)$ (ii) and finally the third one on the last list, i.e. the list that only contains pending formulas with the shape $F_C(\neg \varphi)$ and $F_C(\varphi \wedge \psi)$ (iii). The rule then behaves in the following way: it first tries to develop all formulas in (i). Then, when (i) is empty, it switches to (ii), and when (ii) is empty as well it switches to (iii). The reason for this is that we want to avoid trying all possible combinations of rule application (which might be necessary since we have rules that, when applied, delete all $F$ formulae), therefore we want to develop every unproblematic $F$ formula before we turn to formulas whose treatment might delete other $F$ formulas. 

The following is part of the code that is used to treat the list (i). Let's take the case in which $f$ is a true atom, as an example. What the rule does is: we add $f$ to the list of true atoms only if it is not part of $F$ atoms or $F_C$ atoms. Obviously, if this is not the case, we have a contradiction, and we get a tableau containing just the empty list. This will come in handy later.\\ 

\begin{code}
module Step where

import Formulas
import Tableau
import HelperFunctions

step :: Node  -> [Tableau]
step (Nd i positives negatives falses [] [] []) = [[Nd i positives negatives falses [] [] []]]
step (Nd i positives negatives falses (f:fs) fnegpending fcpending)
  | tlit  f = [[Nd i (removesign f:positives) negatives falses fs fnegpending fcpending | not (elem (removesign f) negatives || elem (removesign f) falses)]]
  | flit  f = [[Nd i positives (removesign f :negatives) falses fs fnegpending fcpending | removesign f `notElem` positives]]
  | fclit  f = [[Nd i positives negatives (removesign f :falses) fs fnegpending fcpending |  removesign f `notElem` positives]]
\end{code}

Let's take a more complicated case, i.e. rule1. We make a case distinction: we can either have a true conjunction, a false disjunction or a provably false disjunction. In the last two cases there is a technicality, i.e. we have to make sure that we put the components in the right list. Take the last case, as an example. The subformulas can either lead to no deletion or -- because they are either of the shape $F_C(\varphi \wedge \psi)$ or of the shape $F_C(\neg \varphi)$ -- to a deletion. Hence we have to put them in the proper list accordingly.\\

\begin{code}
  | rule1 f = if signof f == T then [[Nd i positives negatives falses ([maketrue y | y <-subf $ removesign f]++fs) fnegpending fcpending]]
              else if signof f == F then [[Nd i positives negatives falses ([makenegative y | y <-subf $ removesign f, not (deletewarning ( makenegative y))]++fs) ([makenegative y | y <-subf $ removesign f, deletewarning (makenegative y ) ]++fnegpending) fcpending]]
              else [[Nd i positives negatives falses ([makefalse y | y <-subf $ removesign f, not (deletewarning (makefalse y)) ]++fs) fnegpending ([makefalse y | y <-subf $ removesign f, deletewarning  (makefalse y) ]++fcpending)]]
  | rule2 f = if signof f == T then [[Nd (i++[0]) positives negatives falses (maketrue (head (subf $ removesign f)): fs) fnegpending fcpending, Nd (i++[1]) positives negatives falses (map maketrue (tail (subf (removesign f))) ++ fs) fnegpending fcpending ]]
              else [[Nd (i++[0]) positives negatives falses ([makenegative (head (subf (removesign f))) | not (deletewarning (makenegative (head (subf (removesign f))))) ]++fs) ([makenegative (head (subf (removesign f))) | deletewarning (makenegative (head (subf (removesign f)))) ]++fnegpending) fcpending, Nd (i++[1]) positives negatives falses ([makenegative (last (subf (removesign f))) | not (deletewarning (makenegative (last (subf (removesign f))))) ]++fs) ([makenegative (last (subf (removesign f))) | deletewarning (makenegative (last (subf (removesign f)))) ]++fnegpending) fcpending]]
  | falseneg f = [[Nd i positives [] falses [maketrue (head (subf (removesign f)))] [] fcpending ]]
  | prfalseconj f = [[Nd (i++[0]) positives [] falses [makefalse (head (subf (removesign f))) | not (deletewarning (makefalse (head (subf (removesign f)))) )] [] ([makefalse (head (subf (removesign f))) | deletewarning (makefalse (head (subf (removesign f)))) ]++ fs ), Nd (i++[1]) positives [] falses [makefalse (last (subf (removesign f))) | not (deletewarning (makefalse (last (subf (removesign f)))) )] [] ([makefalse (last (subf (removesign f))) | deletewarning (makefalse (last (subf (removesign f)))) ]++fs) ]]
  | trueneg f = [[Nd i positives negatives falses ([makefalse (head (subf (removesign f))) | not (deletewarning (makefalse (head (subf (removesign f)))) )]++fs) fnegpending ([makefalse (head (subf (removesign f))) | deletewarning (makefalse (head (subf (removesign f)))) ]++fcpending) ]]
\end{code}

What the step rule does on (ii) is slightly different, because -- given that (ii) is a list of formulas $\varphi_1,\dots,\varphi_n$, where $\varphi_i$ has the shape $F(\neg \varphi)$ -- it outputs two tableaux: the first one is the result of applying the $F\neg$ rule to $\varphi_1$, while the second one is the list containing the original node in which $\varphi_1$ has been deleted from (ii), i.e. (ii) consists of $\varphi_2, \dots, \varphi_n$. Of course this behaviour is repeated similarly for this last list, so we again generate two tableaux, one for $\varphi_2$ and another one for $\varphi_3, \dots, \varphi_n$, and so on. The reason is that, whenever we develop one of these $\varphi_i$'s, we automatically lose all the others in the list, as well as all $F$ literals (after all, they are all $F$ formulae), hence -- for a list of $n$ formulas -- there are exactly $n$ cases to explore, which are the $n$ cases where one deletes $\varphi_i$ first. \\
\begin{code}
step (Nd i positives _ falses [] (f:fs) fcpending)
  | tlit  f = undefined
  | flit  f = undefined
  | fclit  f = undefined
  | rule1 f = undefined
  | rule2 f = undefined
  | falseneg f = [[Nd i positives [] falses [maketrue (head (subf (removesign f)))] [] fcpending ] , [Nd i positives [] falses [] fs fcpending]]
  | prfalseconj f = undefined
  | trueneg f = undefined
\end{code}

Lastly, the step rule works on list (iii), i.e. a list that only contains either formulae of shape $F_C(\varphi \wedge \psi)$ or of shape $F_C(\neg \varphi)$. Because when we arrive at this stage we have no formulae in (ii) and we can only delete $F$ literals, and moreover the rules for $F_C(\varphi \wedge \psi)$ and $F_C(\neg \varphi)$ don't lead to any deletion of formulae inside (iii), in this case we don't need the machinery we saw in (ii), we can just tackle them sequentially as we have seen for (i). Besides, this is also the reason why we kept this kind of formulae as the last \say{kind} to be treated by the algorithm. 

So, this is the last part of the step rule:\\

\begin{code}
step (Nd i positives _ falses [] [] (f:fs))
  | tlit  f = undefined
  | flit  f = undefined
  | fclit  f = undefined
  | rule1 f = undefined
  | rule2 f = undefined
  | falseneg f = [[Nd i positives [] falses [maketrue (head (subf (removesign f)))] [] fs ]]
  | prfalseconj f = [[Nd (i++[0]) positives [] falses [makefalse (head (subf (removesign f))) | not (deletewarning (makefalse (head (subf (removesign f)))) )] [] ([makefalse (head (subf (removesign f))) | deletewarning (makefalse (head (subf (removesign f)))) ]++ fs ), Nd (i++[1]) positives [] falses [makefalse (last (subf (removesign f))) | not (deletewarning (makefalse (last (subf (removesign f)))) )] [] ([makefalse (last (subf (removesign f))) | deletewarning (makefalse (last (subf (removesign f)))) ]++fs) ]]
  | trueneg f = undefined
\end{code}
