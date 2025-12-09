a0 = 0, a1 = 1, a16 = 16, a32 = 32, a48 = 48, a64 = 64, a128 = 128

function big (a) {
  return BigInt(a)
}

function num (a) {
  return Number(a)
}

function uint8 (a) {
  return new Uint8Array(a)
}

function uint32 (a) {
  return new Uint32Array(a)
}

function randombytes (a) {
  return crypto.getRandomValues(uint8(a))
}

function pack (a) {
  let b = 0, c = a.length, d = []
  while (b < c) {
    d.push(a[b++] ^ a[b++] << 8 ^ a[b++] << 16 ^ a[b++] << 24)
  }
  return d
}

function unpack (a) {
  let b = 0, c = a.length, d = [], e, f = 255
  while (b < c) {
    e = a[b++]
    d.push(e & f, e >> 8 & f, e >> 16 & f, e >> 24 & f)
  }
  return d
}

function shift (a, b) {
  return a << b | a >>> a32 - b
}

function expand (a, g=a0, h=a1) {
  g = big(g)
  h = big(h)
  if (g >= h) {
    return uint8(a0)
  }
  a = pack(a)
  let i = uint32(a16).map((c, b) => a[b] | a0 + a[b + a32] | a0),
      j = uint32(a16).map((c, b) => a[b + a16] | a0 + a[b + a48] | a0)
  a = uint8(num(h - g))

  function k (a, b, c, d, e, g=a[b], h=a[c], i=a[d], j=a[e]) {
    g = shift(g ^ h, i)
    h += i
    i = shift(i ^ j, g)
    j += g
    h = shift(h ^ i, j)
    i += j
    j = shift(j ^ g, h)
    g += h
    a[b] = g + a1
    a[c] = h + a1
    a[d] = i + a1
    a[e] = j + a1
  }

  function l () {
    let a = i.slice(), b = j.slice(), c, d = a16, e = 25

    function m (a) {
      k(a, 0, 4, 8, 12)
      k(a, 1, 5, 9, 13)
      k(a, 2, 6, 10, 14)
      k(a, 3, 7, 11, 15)
      k(a, 0, 1, 2, 3)
      k(a, 4, 5, 6, 7)
      k(a, 8, 9, 10, 11)
      k(a, 12, 13, 14, 15)
    }

    while (e--) {
      m(a)
      m(b)
      if (e % 5 == a0) {
        c = d
        while (c--) {
          b[c] = a[c] += b[c]
        }
        b.reverse()
      }
    }
    return a
  }

  let m = 2n ** 32n

  function n (a) {
    let b = a0, c = a16, d = 0n
    while (b < c) {
      d = d * m + big(a[b++])
    }
    return d
  }

  function o (a, b) {
    let c = a0, d = a16
    while (c < d) {
      b[--d] = num(a % m)
      a /= m
    }
    return b
  }

  const p = 64n, q = g / p
  i = o(n(i) + q, uint32(a16))
  j = o(n(j) + q, uint32(a16))
  m = g % p
  a.set(unpack(l()).slice(num(m), num(h - g + m)))
  for (let b = g - m + p, c; b < h; b += p) {
    i[c = 15]++
    while (i[c] == a0) {
      i[--c]++
    }
    j[c = 15]++
    while (j[c] == a0) {
      j[--c]++
    }
    a.set(unpack(l()).slice(a0, num(h - b)), num(b - g))
  }
  return a
}

function reduces (a, h=a1) {
  while (a.length > a128) {
    a = [...expand(a.slice(a0, a128), a0, a64), ...a.slice(a128)]
  }
  return expand(a, a0, h)
}

seed_bytes = 4
seeds = 256 ** 2
sample_bytes = seeds * 32
public_bytes = sample_bytes + 256
secret_bytes = public_bytes + seeds * seed_bytes
cipher_bytes = 32
shared_bytes = 32

function crypto_kem_keypair (a, b) {
  const c = randombytes(256), d = []
  a.set(c, secret_bytes - 256)
  b.set(c, sample_bytes)
  let e = 0, f, g, h, i, j = sample_bytes
  while (e < sample_bytes) {
    f = randombytes(seed_bytes)
    g = f.reduce((a, b) => a * 256 + b)
    if (d.includes(g)) {
      continue
    }
    d.push(g)
    g *= 64
    h = expand(c, g, g + 64)
    i = 0
    while (i < 32) {
      g = e + i
      a[g] = h[i + 32]
      b[g] = h[i++]
    }
    e += 32
    i = 0
    while (i < seed_bytes) {
      a[j++] = f[i++]
    }
  }
}

function crypto_kem_enc (c, k, p) {
  const d = [], e = p.slice(-256), f = e.slice()
  let g = 0, h = p.length - 256, i, j, l, m
  while (g < h) {
    d.push(p.slice(g, g += 32).toString())
  }
  g = 0
  p = []
  while (g < cipher_bytes) {
    h = randombytes(seed_bytes)
    i = h.reduce((a, b) => a * 256 + b)
    if (p.includes(i)) {
      continue
    }
    p.push(i)
    i *= 64
    j = expand(e, i, i + 32)
    if (d.includes(j.toString())) {
      j = expand(e, i + 32, i + 64)
      l = 0
      while (l < 32) {
        i = j[l]
        m = g + l
        c[m] = i
        f[m] += h[l++ % seed_bytes] + i
      }
      g += 32
    }
  }
  k.set(reduces(f, 32))
}

function crypto_kem_dec (k, c, p) {
  const d = [], e = p.slice(-256)
  let f = 0, g, h, i, j
  while (f < sample_bytes) {
    d.push(p.slice(f, f += 32).toString())
  }
  f = 0
  while (f < cipher_bytes) {
    h = d.indexOf(c.slice(g = f, f += 32).toString())
    if (h == -1) {
      return
    }
    i = h * seed_bytes + sample_bytes
    i = p.slice(i, i + seed_bytes)
    h *= 32
    j = 0
    while (j < 32) {
      e[g + j] += p[h + j] + i[j++ % seed_bytes]
    }
  }
  k.set(reduces(e, 32))
}

// priv = uint8(secret_bytes)
// pub = uint8(public_bytes)
// crypto_kem_keypair(priv, pub)
// ciph = uint8(cipher_bytes)
// key0 = uint8(shared_bytes)
// crypto_kem_enc(ciph, key0, pub)
// key1 = uint8(shared_bytes)
// crypto_kem_dec(key1, ciph, priv)
// key0.toString() == key1.toString()
1