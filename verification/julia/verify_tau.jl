# verify_tau.jl -- checks of "All tau_k-maximal graphs have the same size" with the pebble game of
# Lee and Streinu, a sparsity test that shares nothing with the subset counts of the other programs.
#
# For a >= 2 the (a, a+1) pebble game accepts an edge set exactly when it is a-sparse
# (e(X) <= a(|X|-1)-1 for |X| >= 2). We check:
#   1. pebble game = subset enumeration on random graphs, 6 <= n <= 11, a = 2..4;
#   2. greedy growth: inserting the edges of K_n in random order, the pebble game always accepts
#      exactly a(n-1)-1 of them, for 2a <= n <= 40 (Theorem 1.1);
#   3. the graph G_0 of Lemma 4.1 is accepted in full and has a(n-1)-1 edges, a = 2..8, n <= 60;
#   4. the count identity and the inequality (y-1)(2a-y) >= 2 of Lemma 4.1 in exact integers.
# Prints "ALL OK" when every check passes.
using Random

failed = false
function check(c, msg)
    global failed
    println(c ? "ok   " : "FAIL ", msg)
    c || (failed = true)
end

mutable struct Pebbles
    k::Int
    l::Int
    peb::Vector{Int}
    out::Vector{Vector{Int}}
end
Pebbles(n, k, l) = Pebbles(k, l, fill(k, n), [Int[] for _ in 1:n])

# move one pebble to u along a directed path, without passing through v
function collect!(G::Pebbles, u, v)
    n = length(G.peb)
    seen = falses(n); seen[u] = true; seen[v] = true
    prev = zeros(Int, n)
    stack = [u]
    while !isempty(stack)
        x = pop!(stack)
        for y in G.out[x]
            seen[y] && continue
            seen[y] = true; prev[y] = x
            if G.peb[y] > 0
                # reverse the path u -> ... -> y; the pebble at y moves to u
                G.peb[y] -= 1; G.peb[u] += 1
                z = y
                while z != u
                    p = prev[z]
                    deleteat!(G.out[p], findfirst(==(z), G.out[p]))
                    push!(G.out[z], p)
                    z = p
                end
                return true
            end
            push!(stack, y)
        end
    end
    return false
end

function insert!(G::Pebbles, u, v)
    while G.peb[u] + G.peb[v] < G.l + 1
        collect!(G, u, v) || collect!(G, v, u) || return false
    end
    if G.peb[u] > 0
        G.peb[u] -= 1; push!(G.out[u], v)
    else
        G.peb[v] -= 1; push!(G.out[v], u)
    end
    return true
end

function pebble_sparse(n, E, a)
    G = Pebbles(n, a, a + 1)
    all(insert!(G, u, v) for (u, v) in E)
end

function subset_sparse(n, E, a)
    adj = zeros(UInt32, n)
    for (u, v) in E
        adj[u] |= UInt32(1) << (v - 1); adj[v] |= UInt32(1) << (u - 1)
    end
    for X in UInt32(1):UInt32((1 << n) - 1)
        s = count_ones(X)
        s < 2 && continue
        e = 0
        for v in 1:n
            (X >> (v - 1)) & 1 == 1 && (e += count_ones(adj[v] & X))
        end
        e ÷ 2 > a * (s - 1) - 1 && return false
    end
    return true
end

rng = MersenneTwister(20261009)
pairs(n) = [(u, v) for u in 1:n for v in u+1:n]

# 1.
let tested = 0, bad = 0, nsparse = 0
    for a in 2:4, n in 6:11, t in 1:150
        p = 0.1 + 0.8 * (t % 15) / 14
        E = [e for e in pairs(n) if rand(rng) < p]
        s = subset_sparse(n, E, a)
        nsparse += s
        tested += 1
        s == pebble_sparse(n, E, a) || (bad += 1)
    end
    check(bad == 0 && 0 < nsparse < tested,
          "pebble game = subset count on $tested random graphs ($nsparse sparse), 6 <= n <= 11")
end

# 2.
let runs = 0, bad = 0
    for a in 2:6, n in 2a:40, t in 1:3
        E = shuffle(rng, pairs(n))
        G = Pebbles(n, a, a + 1)
        m = count(e -> insert!(G, e...), E)
        runs += 1
        m == a * (n - 1) - 1 || (bad += 1)
    end
    check(bad == 0, "greedy growth stops at a(n-1)-1 edges in all $runs runs, 2 <= a <= 6, 2a <= n <= 40")
end

# 3.
let graphs = 0, bad = 0
    for a in 2:8, n in 2a:60
        E = [(u, v) for (u, v) in pairs(n)
             if u <= a || (v <= 2a && !(u == 2a - 1 && v == 2a))]
        graphs += 1
        (length(E) == a * (n - 1) - 1 && pebble_sparse(n, E, a)) || (bad += 1)
    end
    check(bad == 0, "G_0 is a-sparse with a(n-1)-1 edges for all $graphs pairs 2 <= a <= 8, 2a <= n <= 60")
end

# 4.
check(all(binomial(big(n), 2) - binomial(big(n - a), 2) + binomial(big(a), 2) - 1 == a * (n - 1) - 1
          for a in 2:300 for n in 2a:700),
      "C(n,2) - C(n-a,2) + C(a,2) - 1 = a(n-1) - 1 for 2 <= a <= 300, 2a <= n <= 700")
check(all((y - 1) * (2a - y) >= 2 && binomial(y, 2) <= a * (y - 1) - 1 for a in 2:500 for y in 2:2a-1) &&
      all(binomial(2a, 2) - 1 == a * (2a - 1) - 1 for a in 2:500),
      "(y-1)(2a-y) >= 2 and C(y,2) <= a(y-1)-1 for 2 <= y <= 2a-1; equality at y = 2a (a <= 500)")

println(failed ? "SOME CHECKS FAILED" : "ALL OK")
exit(failed ? 1 : 0)
