Tom, Jerry and Spike play the following game. Tom generates a random binary code of length $n$, 
which he sends to Spike along with a *secret number* between $1$ and $n$. 
Spike flips exactly one bit in the code and then sends only the modified binary code to Jerry. 
Is there a pre-established strategy for Spike and Jerry such that Jerry 
can determine the *secret number* solely by looking at the code sent by Spike?

**Theorem:**  
There is a pre-established strategy for Spike and Jerry if and only if $n = 2^m$ for some $m \in \mathbb{N}$.

**Remark:**  
Let $I =$ { $1, \ldots, n$ }, where $n \ge 1$. In the following, we consider 
$\mathbb{Z}_2^m = \mathbb{Z}_2 \times \cdots \times \mathbb{Z}_2$
as a vector space over $\mathbb{Z}_2$, where $m \in \mathbb{N}^*$. For $i \in I$, let 
$e_i \in \mathbb{Z}_2^n$ be the canonical vector 
with $1$ on the $i$-th position and zeros elsewhere. Note that $z + e_i$ is the code $z$ with the $i$-th bit flipped, 
for every $z \in \mathbb{Z}_2^n$ and $i \in I$.  
Spike and Jerry have a pre-established strategy if and only if there exists 
$f : \mathbb{Z}_2^n \to I$ such that for every $z \in \mathbb{Z}_2^n$ and every $k \in I$ 
there exists $i \in I$ such that $f(z + e_i) = k$.

References:
 - https://www.3blue1brown.com/lessons/chessboard-puzzle
 - https://www.youtube.com/watch?v=as7Gkm7Y7h4
