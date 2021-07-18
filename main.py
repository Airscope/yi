import elgamal
import numpy as np
import random
import time

all_items = []

DM_SERVERS_NUMS = 2


def std_item_tbl(xx):
    return hash(xx)


def read_dataset(M, N):
    dataset = []
    items = set()
    row = 0
    # col = 0
    with open('./dataset_chess.txt', 'r') as f:
        for line in f.readlines():
            # transaction = np.zeros(75)
            transaction = set()
            indexs = line.split()
            indexs = indexs[:N]
            for i in indexs:
                transaction.add(std_item_tbl(i))
                items.add(std_item_tbl(i))
            dataset.append(transaction)
            all_items.extend(items)
            row += 1
            if row == M:
                break
    return dataset


def item_dict_anony(possible_items, public_key):
    encrypted_items = []
    items_num = len(possible_items)
    for i in range(items_num):
        ai_code = possible_items[i]  # std_item_tbl[possible_items[i]]
        ci = elgamal.encrypt_int(public_key, ai_code)
        encrypted_items.append(ci)

    for j in range(DM_SERVERS_NUMS):
        # Re-encryption
        for k in range(len(encrypted_items)):
            encrypted_items[k] = elgamal.reencrypt(public_key, encrypted_items[k])
        # Shuffling
        random.shuffle(encrypted_items)
        if j < DM_SERVERS_NUMS - 1:
            print("forward results from server", j, "to", j + 1)

    return encrypted_items


def reencrypt_set(s: set, public_key):
    cipher_set = set()
    for entry in s:
        cipher_set.add(elgamal.reencrypt(public_key, entry))
    return cipher_set


def trans_anony(trans, public_key):
    lambda_ = len(trans)  # trans = [[{1},{2}],[{1,2},{3,4}]]
    anonymized_trans = []
    for _ in range(lambda_):
        anonymized_trans.append([])

    for eta in range(len(trans)):
        # transaction anonymization
        l_eta = len(trans[eta])
        for i in range(DM_SERVERS_NUMS):
            for j in range(l_eta):
                s = set()
                for c in trans[eta][j]:
                    if c.__class__ == int:
                        s.add(tuple(elgamal.encrypt_int(public_key, c)))
                    else:
                        s.add(tuple(elgamal.reencrypt(public_key, c)))
                anonymized_trans[eta].append(s)
                tmp = list(anonymized_trans[eta][j])
                random.shuffle(tmp)
                # print("Randomly shuffling items")

            random.shuffle(anonymized_trans[eta])

            if i < DM_SERVERS_NUMS - 1:
                print("Forward T'_", eta, "to server ", i + 1)

    return anonymized_trans  # [[{},{}],[{},{}]]


def add_extra_random_trans_in(extra_trans_num: int, items_num: int, trans_with_i_items):
    for _ in range(extra_trans_num):
        # generate a set with items_num length
        random_set = set()
        for __ in range(items_num):
            random_set.add(random.choice(all_items))
        trans_with_i_items.append(random_set)


# trans_database = [{},{},{}]
def add_noisy_trans(trans_database):
    phi = 1 / DM_SERVERS_NUMS
    grouped_trans = []

    lambda_ = -1
    for trans in trans_database:
        if len(trans) > lambda_:
            lambda_ = len(trans)

    for _ in range(lambda_):
        grouped_trans.append([])

    for trans in trans_database:
        grouped_trans[len(trans) - 1].append(trans)

    # Each DM Server does:
    for _ in range(DM_SERVERS_NUMS):
        # add noisy transactions
        for i in range(lambda_):
            extra_trans_num = np.ceil(phi * len(grouped_trans[i]))
            add_extra_random_trans_in(int(extra_trans_num), i + 1, grouped_trans[i])
    return grouped_trans


def modexp(base, exp, modulus):
    if exp < 0:
        return pow(base, modulus - 1 + exp, modulus)
    # if exp == -1:
    #    return pow(base, modulus-2, modulus) # modulus is prime and base is relatively prime with modulus
    return pow(base, exp, modulus)


def PET(cipher1, cipher2, private_key):
    A = 1
    B = 1
    for i in range(DM_SERVERS_NUMS):
        r_i = random.randint(0, private_key.p)
        A_1 = cipher1[0]
        B_1 = cipher1[1]
        A_2 = cipher2[0]
        B_2 = cipher2[1]
        temp1 = modexp(A_1, r_i, private_key.p)
        temp2 = modexp(A_2, r_i, private_key.p)
        A_i = (temp1 / temp2) % private_key.p
        temp1 = modexp(B_1, r_i, private_key.p)
        temp2 = modexp(B_2, r_i, private_key.p)
        B_i = (temp1 / temp2) % private_key.p
        A *= A_i
        B *= B_i

    C = [A, B]
    decrypted = elgamal.decrypt_int(private_key, C)
    if decrypted == 1:
        return 1
    else:
        return 0


# transactions = [{},{},...{}]
def replace(transactions: list, src, target):
    result = transactions.copy()
    for i in range(len(transactions)):
        if src in transactions:
            result[i].remove(src)
            result[i].add(target)
    return result


def same_item_ident_based_dict(encrypted_items, divided_database, private_key):
    result_database = []
    # result_database = [[{},{}], [{},{},{}], ...]

    # for _ in range(len(divided_database)):
    #     result_database.append([])

    for i in range(DM_SERVERS_NUMS):
        for j in range(len(encrypted_items)):
            for tran in divided_database[i]:
                c_j = encrypted_items[j]
                # print("c_j", c_j)
                # print("c", tran)
                for c in list(tran):
                    if PET(c_j, list(c), private_key) == 1:
                        # S_i replaces c in D''_i with c_j
                        result_database.append(replace(divided_database[i], list(c), c_j))
    return result_database


def is_noisy_set(s: set):
    return random.choice([True, False])


def to_binary(length, num):
    res = []
    for i in range(length):
        res.append((num >> i) & 1)
    return res


def frequent_itemset_mining(k_itemset: set, D_deriv_deriv, T_deriv_deriv, enc_bin_minsupp, public_key, private_key):
    F = 0
    F_i = []
    f_i = []
    for i in range(DM_SERVERS_NUMS):
        F_i.append(0)
        f_i.append(0)
        for s in D_deriv_deriv[i]:
            if k_itemset.issubset(s):
                F_i[i] += 1
                if is_noisy_set(s):
                    f_i[i] += 1
        F += F_i[i] - f_i[i]
    m_deriv = int(np.ceil(np.log2(len(T_deriv_deriv))) + 1)
    m = len(enc_bin_minsupp)
    # bin_F = to_binary(m_deriv, F)

    return private_cmp_2(enc_bin_minsupp, F_i, f_i, m_deriv, m, public_key, private_key)


def private_cmp_2(enc_bin_minsupp, F_i, f_i, m_deriv, m, public_key, private_key):
    enc_neg_delta_compl = []
    enc_1 = [elgamal.encrypt_int(public_key, 1) for _ in range(m_deriv - 1)]
    enc_1.append(elgamal.encrypt_int(public_key, public_key.g))

    enc_g = elgamal.encrypt_int(public_key, public_key.g)

    for i in range(m_deriv + 1):
        if i < m:
            enc_neg_delta_compl.append(elgamal.divide(enc_g, enc_bin_minsupp[i], public_key))
        else:
            enc_neg_delta_compl.append(enc_g)
    enc_z = enc_neg_delta_compl[::-1]

    enc_Fi_minus_fi = []
    for i in range(DM_SERVERS_NUMS):
        v_m_deriv_i = 0 if F_i[i] - f_i[i] >= 0 else 1
        bin_Fi_minus_fi = [v_m_deriv_i] + to_binary(m_deriv, F_i[i] - f_i[i])
        # print(bin_Fi_minus_fi)
        enc_bin_Fi_minus_fi = [elgamal.encrypt_int(public_key, modexp(public_key.g, vi, public_key.p)) for vi in
                               bin_Fi_minus_fi]

        enc_z = add(enc_z, enc_bin_Fi_minus_fi, public_key, private_key)

    g_z_mderiv = elgamal.decrypt_int(private_key, enc_z[0])
    z_mderiv = 0 if g_z_mderiv == 1 else -1
    belta = 1 if z_mderiv == 0 else 0
    return belta


# Input: E(g^a), E(g^b), a <-- {-1,1} b <-- {Z_q}
# Output: E(g^ab)
def conditional_gate(enc_g_a, enc_g_b, public_key, private_key):
    # U = elgamal.encrypt_int(public_key, modexp(public_key.g, a, public_key.p))
    # V = elgamal.encrypt_int(public_key, modexp(public_key.g, b, public_key.p))
    U = enc_g_a
    V = enc_g_b
    for i in range(DM_SERVERS_NUMS):
        r_i = random.choice([-1, 1])
        # print(U[0])
        U_exp_ri = [modexp(U[0], r_i, public_key.p), modexp(U[1], r_i, public_key.p)]
        V_exp_ri = [modexp(V[0], r_i, public_key.p), modexp(V[1], r_i, public_key.p)]
        U = elgamal.reencrypt(public_key, U_exp_ri)
        V = elgamal.reencrypt(public_key, V_exp_ri)
    decrypted = elgamal.decrypt_int(private_key, U)
    a_deriv = 1 if decrypted == public_key.g else -1
    W = [modexp(V[0], a_deriv, public_key.p), modexp(V[1], a_deriv, public_key.p)]

    return W


def add(enc_binary_x, enc_binary_y, public_key, private_key):
    assert (len(enc_binary_y) == len(enc_binary_x))
    m = len(enc_binary_x)
    enc_g_ciminus1 = elgamal.encrypt_int(public_key, 1)
    enc_g_ci = enc_g_ciminus1
    enc_z = []
    for i in range(m):
        enc_g_xiyi = conditional_gate(enc_binary_x[i], enc_binary_y[i], public_key, private_key)
        enc_g_xiciminus1 = conditional_gate(enc_binary_x[i], enc_g_ciminus1, public_key, private_key)
        enc_g_yiciminus1 = conditional_gate(enc_binary_y[i], enc_g_ciminus1, public_key, private_key)
        enc_g_neg2 = elgamal.encrypt_int(public_key, modexp(public_key.g, -2, public_key.p))
        enc_g_neg2xi = conditional_gate(enc_g_neg2, enc_binary_x[i], public_key, private_key)
        enc_g_neg2xiyicminus1 = conditional_gate(enc_g_neg2xi, enc_g_yiciminus1, public_key, private_key)

        tmp1 = elgamal.multiply(enc_g_xiyi, enc_g_xiciminus1, public_key)
        tmp2 = elgamal.multiply(enc_g_yiciminus1, enc_g_neg2xiyicminus1, public_key)
        enc_g_ci = elgamal.multiply(tmp1, tmp2, public_key)

        enc_g_neg2ci = conditional_gate(enc_g_neg2, enc_g_ci, public_key, private_key)

        tmp1 = elgamal.multiply(enc_binary_x[i], enc_binary_y[i], public_key)
        tmp2 = elgamal.multiply(enc_g_ciminus1, enc_g_neg2ci, public_key)
        enc_g_zi = elgamal.multiply(tmp1, tmp2, public_key)
        enc_z.append(enc_g_zi)
        enc_g_ci = enc_g_ciminus1
    # enc_z.append(enc_g_ci)
    enc_z = enc_z[::-1]
    return enc_z


def main():
    print("Key Generation...")
    keys = elgamal.generate_keys()

    private_key = keys['privateKey']  # x
    public_key = keys['publicKey']


    M = 1000
    for N in range(10, 41, 10):
        print("****************************\nM = ", M, ", N = ", N)
        origin_trans_database = read_dataset(M, N)  # [{},{},{}]

        time_start = time.time()

        # Item dictionary anonymization
        print("----------------\nItem dictionary anonymization...")
        encrypted_items = item_dict_anony(all_items, public_key)

        # Transaction anonymization
        print("----------------\nTransaction anonymization...")
        noisy_trans = add_noisy_trans(origin_trans_database)  # [ [{},{}], [{}], [{},{},{}] ]
        D_deriv = trans_anony(noisy_trans, public_key)
        temp_trans = []
        for t in D_deriv:
            temp_trans.extend(t)
        random.shuffle(temp_trans)
        divided_trans = [temp_trans[i::DM_SERVERS_NUMS] for i in range(DM_SERVERS_NUMS)]

        # Same Item Identification Based on Dictionary
        print("----------------\nSame Item Identification...")
        D_deriv_deriv = same_item_ident_based_dict(encrypted_items, divided_trans, private_key)

        # Frequent itemset mining
        one_itemset = {tuple(elgamal.encrypt_int(public_key, 1))}
        minsupp = 100
        bin_minsupp = to_binary(int(np.log2(minsupp) + 1), minsupp)
        enc_bin_minsupp = [elgamal.encrypt_int(public_key, modexp(public_key.g, bin_minsupp[i], public_key.p)) for i in
                           range(len(bin_minsupp))]
        print("----------------\nFrequent Itemset Mining...")
        result = frequent_itemset_mining(one_itemset, D_deriv_deriv, D_deriv, enc_bin_minsupp, public_key, private_key)

        time_end = time.time()
        secs = time_end - time_start
        print("Mining Result = ", result, "\nTime cost", secs, "seconds, that is", secs / 60,
              "minutes\n*************************")


main()
