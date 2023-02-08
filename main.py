#  Luiza de Araújo Nunes Gomes
#  Matrícula: 190112794

#  use o pip install pyasn1==0.4.5 para rodar o projeto
import base64
import hashlib
import os
import random
import pyasn1.codec.der.encoder
import pyasn1.codec.der.decoder
import pyasn1.type.univ
import numpy as np


# # # # # # # # # # # # # # # # # # # # # # # # # # # 
# # # # # # # # # Modular  Calculus # # # # # # # # # 
# # # # # # # # # # # # # # # # # # # # # # # # # # # 
def gcd_calculus(x, y):
    if x== 0:
        return (y, 0, 1)
    else:
        d, b, a = gcd_calculus(y % x, x)
        return (d, a - (y // x) * b, b)

def lcm_calculus(x, y):
   return (x*y)//gcd_calculus(x,y)

def mod_inverse(a, m):
    d, x, y = gcd_calculus(a, m)
    if d == 1:
        return x % m

# # # # # # # # # # # # # # # # # # # # # # # # # # # 
# # # # # # # # # # X XOR Y # # # # # # # # # # # # #
# # # # # # # # # # # # # # # # # # # # # # # # # # # 
def byte_xor(x, y):
    return bytes([_x1 ^ _y1 for _x1, _y1 in zip(x, y)])

# # # # # # # # # # # # # # # # # # # # # # # # # # # 
# # Esta função passa os dados dos txts em string # #
# # # # # # # # # # # # # # # # # # # # # # # # # # #   
def get_data_from_txt(file):
    data = []
    with open(file, 'r') as projectfile:
        for line in projectfile:
            line = line.replace("\n", "")
            data.append(line)
    return " ".join(data)



# # # # # # # # # # # # # # # # # # # # # # # # # # # # 
# # # OAEP(Optimal Asymmetric Encryption Padding) # # #
# # # # # # # # # # # # # # # # # # # # # # # # # # # #

# # # # # # # # # # # # # # # # # # # # # # # # # # #     
# # # # # #  Hash Function for SHA3 # # # # # # # # # 
# # # # # # # # # # # # # # # # # # # # # # # # # # # 
def sha3(m):
    hash = hashlib.sha3_256()
    if type(m) == str:
        m = m.encode('utf-8')
    hash.update(m)
    return hash.digest()

# Mask Generator Function
# input
# Z: seed from which mask is generated, an octet string
# l: intended length in octets of the mask, at most (2**32)*hLen
# Output
# mask: mask, an octet string of length l ==> T
# Errors: ‘‘mask too long’’
def mgf(Z, l):
    T = b''
    hLen =  sha3(T)
    hLen = len(hLen)
    if (l > (hLen << 32)):
        raise ValueError("mask too long")
    counter = 0
    while (len(T)< l):
        cipher = int.to_bytes(counter, 4, 'big')
        add = str(Z + cipher)
        Tadd = sha3(add)
        T = T + Tadd
        counter += 1
    return T[:l]
# OAEP Encoding
# Input
# k: length of the RSA modulus n in bytes
# M: message to be padded (at most k − 2*hLen - 2 bytes)
# Output
# EM: Encrypted Message
# Afins:
# hLen: length of the output of the hash function in bytes
def OAEP_encoding(M, k, label):
    mEncoded = M.encode('utf-8')
    mLen = len(mEncoded)
    lHash = sha3(label)
    hLen = len(lHash)
    PS = b'\x00'*(k - mLen - 2*hLen - 2)
    DB = PS + b'\x01'+ mEncoded
    seed = os.urandom(hLen)
    dbMask = bytes(mgf(seed, k- hLen -1))
    maskedDB = byte_xor(DB, dbMask)
    seedMask = bytes(mgf(maskedDB, hLen))
    maskedSeed = byte_xor(seed, seedMask)
    EM = b'\x00' + maskedSeed + maskedDB
    return EM

# OAEP Decoding // Funciona com Label
# l == label
# EME-OAEP decoding
def OAEP_decoding(EM, k, label):
    labelLen = len(label)
    labelDecoded = label.encode('utf-8')
    lHash = sha3(labelDecoded)
    hLen = len(lHash)
    notused, maskedSeed, maskedDB = EM[:labelLen],  EM[labelLen:(labelLen + hLen)], EM[(labelLen+hLen):]
    seedMask = mgf(maskedDB, hLen)
    seed = byte_xor(maskedSeed, seedMask)
    dbMask = mgf(seed, k - len(lHash) - 1)
    DB = byte_xor(maskedDB, dbMask)
    mLen = hLen          #   ponto de início, que é o tamanho do DB
    while mLen < len(DB):
        if DB[mLen] == 0:
            mLen += 1
            continue
        elif DB[mLen] == 1:
            mLen += 1
            break
        else:
            raise Exception()
    M = DB[mLen:]
    return M.decode()


# # # # # # # # # # # # # # # # # # # # # # # # # # # 
# # # # # # RSA (Rivest-Shamir-Adleman) # # # # # # # 
# # # # # # # # # # # # # # # # # # # # # # # # # # # 
# Encoding:     m = M^e mod N
def RSA_encoding(m, N, e):
    M = pow(m, e, N)
    return M

# Decoding exponent:    d = e^-1 mod (p-1)(q-1)
# Decoding:     m = M^d mod N
def RSA_decoding(N, e, M, p, q):
    d = mod_inverse(e, ((p-1)*(q-1)))
    m = pow(M, d, N)
    return m




# definição de primos com no mínimo 1024 bits
# MILLER RABIN: para testar se realmente é número primo
# n: number to test
# k: times you wanna test it
def miller_rabin(n, k):
    if (n%2 == 0) or (n <2):
        return False
    if n == 3:
        return True
    p = n - 1
    q = 0
    while (p%2 == 0):                       # até p ser um número par
        p = p // 2
        q += 1
    for i in range(k):                      # times that the numbers are tested
        a = random.randrange(2, n - 1)      # random number
        x = pow(a, p, n)                    # a**p mod n
        if (x != 1):
            j = 0
            while (x != ( n - 1)):          # while x is not equal to the largest number possible of a
                if (j == q - 1):            
                    return False
                else:
                    x = (x**2)%n            # (x**2) mod n
                    j = j + 1               
    return True

# Método do MILLER RABIN: para procurar um número de início para encontrar p e q
# n: number to test
# k: times you wanna test it
def mr_help_pandq(n, k):
    p = n - 1
    q = 0
    if n == 3:
        return 3
    while (p%2 == 0):                       # até p ser um número par
        p = p // 2
        q += 1
    for i in range(k):                      # times that the numbers are tested
        a = random.randrange(2, n - 1)      # random number
        x = pow(a, p, n)                    # a**p mod n
        if (x != 1):
            j = 0
            while (x != ( n - 1)):          # while x is not equal to the largest number possible of a
                if (j == q - 1):            
                    return p, q
                else:
                    x = (x**2)%n            # (x**2) mod n
                    j = j + 1               
    if p > q:
        return p
    else:
        return q



# Large Prime Generator
# input
# k: number of bits, of minimum 1024 bits in decimal
# output
# n: random number of k bits
def generateLargePrime(k=1024):
    while (1):
        n = random.randrange(2**(k-1), 2**(k))
        if miller_rabin(n, 100):
            return n

# Finding p and q from N
# gcd_calculus(e, (i-1)*(j-1)) == 1) and (i*j == N) and is_prime(i) and is_prime(j) and i.bit_length()== 1024 and j.bit_length()==1024
def find_p_and_q(e, N):
    p = 0
    q = 0
    use = mr_help_pandq(N, 10)
    p = generateLargePrime()
    q = generateLargePrime()
    tested = []
    pq = (p, q)
    while ((pq not in tested) and (q*p != N) and (gcd_calculus(e, (p-1)*(q-1))[0] != 1)):
        p = generateLargePrime()
        q = generateLargePrime()
        tested.append((p, q))
    return p, q

# # # # # # # # # # # # # # # # # # # # # # # # # # # 
# # # # # # # # # # # # # # # # # # # # # # # # # # # 
# Integer-to-Octet-String primitive
# Input
# x: nonnegative integer to be converted
# l: intended length of the resulting octet string
# Output
# X: corresponding octet string of length l
def i2osp(x, l):
    return x.to_bytes(l, byteorder='big')

# Octet-String-to-Integer primitive
# Input
# X: octet string to be converted
# Output
# corresponding nonnegative integer
def os2ip(X):
    return int.from_bytes(X, byteorder='big')

# # # # # # # # # # # # # # # # # # # # # # # # # # # 
# # # # # # # # GET PUBLIC KEY LENGTH # # # # # # # #
# # # # # # # # # # # # # # # # # # # # # # # # # # #
def keyLength(N, eord):
    length = N.bit_length()//8
    return length

# # # # # # # # # # # # # # # # # # # # # # # # # # # # 
# # # # # # # # # # # ( RSA-OAEP) # # # # # # # # # # # 
# # # # # # # # # # # # # # # # # # # # # # # # # # # #

# Encryption/Decryption Operation
# # RSA Encryption # #
# Input
# publicKey: (N, e) => recipient’s RSA public key
# M: message to be encrypted, an octet string of length at most k − 2 − 2hLen, where k is the length in octets of the modulus n and hLen is the length in octets of the hash function output for EME-OAEP.
# Output
# EM: ciphertext, an octet string of length k
def RSA_encryption(N, e, M):
    # tratar o N para melhor ler
    k = keyLength(N, e)
    EM = RSA_encoding(os2ip(M), N, e)
    return base64.b64encode(str(EM).encode())

# # RSA-OAEP Encryption # #
# Input
# publicKey: (N, e) => recipient’s RSA public key
# M: message to be encrypted, an octet string of length at most k − 2 − 2hLen, where k is the length in octets of the modulus n and hLen is the length in octets of the hash function output for EME-OAEP.
# Output
# encrypted message with RSA-OAEP encryption
def RSA_OAEP_encryption(publicKey, M):
    n, e = publicKeyPEMTranslator(publicKey)
    k = keyLength(n, e)
    encoded = OAEP_encoding(M, k, 'b')
    return RSA_encryption(n, e, encoded)

# # RSA Decryption # #
# Input
# k: recipient’s RSA private key
# EM: ciphertext to be decrypted, an octet string of length k, where k is the length in octets of the modulus n
# Output
# M: message, an octet string of length at most k − 2 − 2hLen, where hLen is the length in octets of the hash function output for EME-OAEP
def RSA_decryption(N, d, EM, p, q):
    k = keyLength(N, d)
    M = RSA_decoding(N, d, os2ip(EM), p, q)
    return i2osp(M, 256)

# # RSA-OAEP Decryption # #
# Input
# privateKey: (N, e) => recipient’s RSA public key
# EM: ciphertext to be decrypted, an octet string of length k, where k is the length in octets of the modulus n
# Output
# message, an octet string of length at most k − 2 − 2hLen, where hLen is the length in octets of the hash function output for EME-OAEP
def RSA_OAEP_decryption(privateKey, EM):
    N, e, d, p, q, dP, dQ, qInv = privateKeyPEMTranslator(privateKey)
    k = keyLength(N, d)
    decoded = RSA_decryption(N, d, EM, p, q)
    return OAEP_decoding(decoded, 256, 'b')

# # # # # # # # # # # # # # # # # # # # # # # # # # # # 
# # # # # # # Generating a RSA Key Pair # # # # # # # #
# # # # # # # # # # # # # # # # # # # # # # # # # # # #

# # # # # # # # # # # PublicKey # # # # # # # # # # # #
# # # # # # # # # # # # # # # # # # # # # # # # # # # #
def publicKeyPEM(n, e):
    X = pyasn1.type.univ.Sequence()
    for x in [n, e]:
        lenX = len(X)
        X.setComponentByPosition(lenX, pyasn1.type.univ.Integer(x))
    pk = pyasn1.codec.der.encoder.encode(X)
    return '-----BEGIN RSA PUBLIC KEY-----\n{}-----END RSA PUBLIC KEY-----\n'.format(base64.encodebytes(pk).decode('ascii'))

# # # # # # # # # # # GetValues # # # # # # # # # # # #    
# # # # # # # # # # # PublicKey # # # # # # # # # # # #
# # # # # # # # # # # # # # # # # # # # # # # # # # # #
def publicKeyPEMTranslator(publicKey):
    publicKey = publicKey.replace('-----BEGIN RSA PUBLIC KEY-----\n', '')
    publicKey = publicKey.replace('-----END RSA PUBLIC KEY-----\n', '')
    pk = ''.join(publicKey.split('\n'))
    pk1, restofinput = pyasn1.codec.der.decoder.decode(base64.decodebytes(pk.encode('ascii')))
    n = int(pyasn1.type.univ.Integer(pk1[0]))
    e = int(pyasn1.type.univ.Integer(pk1[1]))
    return n, e


# # # # # # # # # # # Private Key # # # # # # # # # # #
# # # # # # # # # # # # # # # # # # # # # # # # # # # #
# INPUT
# p: the first factor, a nonnegative integer
# q: the second factor, a nonnegative integer
# dP: the first factor’s exponent, a nonnegative integer
# dQ: the second factor’s exponent, a nonnegative integer
# qInv: the CRT coefficient, a nonnegative integer
def privateKeyPEM(n, e, d, p, q, dP, dQ, qInv):
    X = pyasn1.type.univ.Sequence()
    sequence = [0, n, e, d, p, q, dP, dQ, qInv]
    for x in sequence:
        lenX = len(X)
        X.setComponentByPosition(lenX, pyasn1.type.univ.Integer(x))
    pk = pyasn1.codec.der.encoder.encode(X)
    return '-----BEGIN RSA PRIVATE KEY-----\n{}-----END RSA PRIVATE KEY-----\n'.format(base64.encodebytes(pk).decode('ascii'))

# # # # # # # # # # # Get  Values # # # # # # # # # # #
# # # # # # # # # # # Private Key # # # # # # # # # # #
# # # # # # # # # # # # # # # # # # # # # # # # # # # #
# INPUT
# p: the first factor, a nonnegative integer
# q: the second factor, a nonnegative integer
# dP: the first factor’s exponent, a nonnegative integer
# dQ: the second factor’s exponent, a nonnegative integer
# qInv: the CRT coefficient, a nonnegative integer
def privateKeyPEMTranslator(privateKey):
    privateKey = privateKey.replace('-----BEGIN RSA PRIVATE KEY-----\n', '')
    privateKey = privateKey.replace('-----END RSA PRIVATE KEY-----\n', '')
    pk = ''.join(privateKey.split('\n'))
    pk1, restofinput = pyasn1.codec.der.decoder.decode(base64.decodebytes(pk.encode('ascii')))
    zero = int(pyasn1.type.univ.Integer(pk1[0]))
    n = int(pyasn1.type.univ.Integer(pk1[1]))
    e = int(pyasn1.type.univ.Integer(pk1[2]))
    d = int(pyasn1.type.univ.Integer(pk1[3]))
    p = int(pyasn1.type.univ.Integer(pk1[4]))
    q = int(pyasn1.type.univ.Integer(pk1[5]))
    dP = int(pyasn1.type.univ.Integer(pk1[6]))
    dQ = int(pyasn1.type.univ.Integer(pk1[7]))
    qInv = int(pyasn1.type.univ.Integer(pk1[8]))
    return n, e, d, p, q, dP, dQ, qInv

# RSA Key Generation Random
# Input
# L: the desired bit length for the modulus
# Output
# K: a valid private key e*d = 1 (mod LCM(p-1, q-1))
# e: the public exponent, an odd integer greater than 1
# (n, e): a valid public key
def RSAKGRand(L):
    p = 0
    q = 0
    while p == q and (p*q).bit_length() != 1024 and miller_rabin(p, 10) == False and miller_rabin(q, 10) == False:
        p = generateLargePrime()
        q = generateLargePrime()
    n = p * q
    phi = (p - 1) * (q - 1)
    e = 65537
    d = mod_inverse(e, phi)
    dP = mod_inverse(e, (p-1))
    dQ = mod_inverse(e, (q-1))
    qInv = mod_inverse(q, p)
    publicKey = publicKeyPEM(n, e)
    public = open("publicKey.txt", "w")
    public.write(publicKey)
    public.close()
    privateKey = privateKeyPEM(n, e, d, p, q, dP, dQ, qInv)
    private = open("privateKey.txt", "w")
    private.write(privateKey)
    private.close()
    return publicKey, privateKey

# RSA Key Generation Not Random
# Input
# p, q and e
# Output
# K: a valid private key e*d = 1 (mod LCM(p-1, q-1))
# e: the public exponent, an odd integer greater than 1
# (n, e): a valid public key
def RSAKGInput(p, q, e):
    n = p * q
    phi = (p - 1) * (q - 1)
    d = mod_inverse(e, phi)
    dP = mod_inverse(e, (p-1))
    dQ = mod_inverse(e, (q-1))
    qInv = mod_inverse(q, p)
    publicKey = publicKeyPEM(n, e)
    public = open("publicKey.txt", "w")
    public.write(publicKey)
    public.close()
    privateKey = privateKeyPEM(n, e, d, p, q, dP, dQ, qInv)
    private = open("privateKey.txt", "w")
    private.write(privateKey)
    private.close()
    return publicKey, privateKey

def interface_rsae_oaep():
    one = get_data_from_txt('one.txt')
    two = get_data_from_txt('two.txt')
    n = 131996649081988309815009412231606409998872008467220356704480658206329986017741425592739598784901147490262698283265202147593817926551998457936217729984043905483806898514062338649654338829045552688587285851621946053376392312680578795692682905599590422046720587710762927130740460442438533124053848898103790124491
    e = 17
    p, q = 12507560385898395063155377438652785015406816933846982747539518586622849241981265061903326335357883560741496856341342737342150564026983421615432869995046297, 10553348935321349098708401203217373529736516872897815887866666361622732987827061646884190485302047334528175415912687182844924393023674139906406943407084803
    publicKey, privateKey = RSAKGInput(p, q, e)
    i = 12
    while (i != 0):
        print("Escolha uma das opções, e digite o número que indica esta:\n1 => Codificar e Decodificar em OAEP\n2 => Codificar e Decodificar em RSA Simples\n3 => Cifração/decifração assimétrica RSA usando OAEP\n4 => Criação de Chaves Públicas e Privas\n0 => Fechar interface")
        i = int(input())
        if i == 1:
            print("Escolha qual arquivo:\n1 => Arquivo somente de Texto || 2 => Arquivo somente com números")
            j = 0
            while j != 1 or j != 2:
                j = int(input())
                if j == 1:
                    A = OAEP_encoding(one, 256, 'b')
                    print("Codificado em OAEP:\n", A)
                    print("Decodificado em OAEP:\n", OAEP_decoding(A, 256, 'b'))
                    break
                if j == 2:
                    B = OAEP_encoding(two, 256, 'b')
                    print("Codificado em OAEP:\n", B)
                    print("Decodificado em OAEP:\n", OAEP_decoding(B, 256, 'b'))
                    break
        if i == 2:
            j = 0
            print("Escolha qual arquivo:\n1 => Arquivo somente com números")
            while j != 1:
                j = int(input())
                if j == 1:
                    B = RSA_encoding(int(two), n, e)
                    print("Codificado em RSA:\n", B)
                    print("Decodificado em RSA:\n", RSA_decoding(n, e, B, p, q))
                    break
        if i == 3:
            j = 0
            print("Escolha qual arquivo:\n1 => Arquivo somente de Texto || 2 => Arquivo somente com números")
            while j != 1 or j != 2:
                j = int(input())
                print("Está criando uma chave pública e uma privada. Checar arquivos criados.")
                if j == 1:
                    A = RSA_OAEP_encryption(publicKey, one)
                    print("Codificado em RSAOAEP:\n", A.decode())
                    print("Decodificado em RSA-OAEP:\n", RSA_OAEP_decryption(privateKey, A))
                    break
                if j == 2:
                    B = RSA_OAEP_encryption(publicKey, two)
                    print("Codificado em RSA-OAEP:\n", B.decode())
                    print("Decodificado em RSA-OAEP:\n", RSA_OAEP_decryption(privateKey, B))
                    break
        if i == 4:
            j = 0
            print("Escolha qual arquivo:\n1 => Aleatória || 2 => Com as informações utilizadas até agora")
            while j != 1 or j != 2:
                j = int(input())
                if i == 1:
                    publicKey, privateKey = RSAKGRand(1024)
                    print("Está criando uma chave pública e uma privada. Checar arquivos criados.")
                    print(publicKey, privateKey)
                    break
                if i == 2:
                    publicKey, privateKey = RSAKGInput(p, q, e)
                    print("Está criando uma chave pública e uma privada. Checar arquivos criados.")
                    print(publicKey, privateKey)
                    break

interface_rsae_oaep()