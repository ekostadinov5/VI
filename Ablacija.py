from math import exp
from random import random, seed


# Иницијализација на мрежа
# Ставете фиксни тежини од 0.5 на code.finki.ukim.mk ако постои проблем со random()
def initialize_network(n_inputs, n_hidden, n_outputs):
    """Изградба на мрежата и иницијализација на тежините

    :param n_inputs: број на неврони во влезниот слој
    :type n_inputs: int
    :param n_hidden: број на неврони во скриениот слој
    :type n_hidden: int
    :param n_outputs: број на неврони во излезниот слој
                      (број на класи)
    :type n_outputs: int
    :return: мрежата како листа на слоеви, каде што секој
             слој е речник со клуч 'weights' и нивните вредности
    :rtype: list(list(dict(str, list)))
    """
    network = list()
    hidden_layer = [{'weights': [random() for _ in range(n_inputs + 1)]}
                    for _ in range(n_hidden)]
    network.append(hidden_layer)
    output_layer = [{'weights': [random() for _ in range(n_hidden + 1)]}
                    for _ in range(n_outputs)]
    network.append(output_layer)
    return network


def neuron_calculate(weights, inputs):
    """Пресметување на вредноста за активација на неврон

    :param weights: даден вектор (листа) на тежини
    :type weights: list(float)
    :param inputs: даден вектор (листа) на влезови
    :type inputs: list(float)
    :return: пресметка на невронот
    :rtype: float
    """
    activation = weights[-1]
    for i in range(len(weights) - 1):
        activation += weights[i] * inputs[i]
    return activation


def sigmoid_activation(activation):
    """Sigmoid активациска функција

    :param activation: вредност за активациската функција
    :type activation: float
    :return: вредност добиена од примена на активациската
             функција
    :rtype: float
    """
    return 1.0 / (1.0 + exp(-activation))


def forward_propagate(network, row):
    """Пропагирање нанапред на влезот кон излезот на мрежата

    :param network: дадената мрежа
    :param row: моменталната податочна инстаца
    :return: листа на излезите од последниот слој
    """
    inputs = row
    for layer in network:
        new_inputs = []
        for neuron in layer:
            activation = neuron_calculate(neuron['weights'], inputs)
            neuron['output'] = sigmoid_activation(activation)
            new_inputs.append(neuron['output'])
        inputs = new_inputs
    return inputs


def sigmoid_activation_derivative(output):
    """Пресметување на изводот на излезот од невронот

    :param output: излезни вредности
    :return: вредност на изводот
    """
    return output * (1.0 - output)


def backward_propagate_error(network, expected):
    """Пропагирање на грешката наназад и сочувување во невроните

    :param network: дадена мрежа
    :type network: list(list(dict(str, list)))
    :param expected: очекувани вредности за излезот
    :type expected: list(int)
    :return: None
    """
    for i in reversed(range(len(network))):
        layer = network[i]
        errors = list()
        if i != len(network) - 1:
            for j in range(len(layer)):
                error = 0.0
                for neuron in network[i + 1]:
                    error += (neuron['weights'][j] * neuron['delta'])
                errors.append(error)
        else:
            for j in range(len(layer)):
                neuron = layer[j]
                errors.append(expected[j] - neuron['output'])
        for j in range(len(layer)):
            neuron = layer[j]
            neuron['delta'] = errors[j] * sigmoid_activation_derivative(neuron['output'])


def update_weights(network, row, l_rate):
    """Ажурирање на тежините на мрежата со грешката

    :param network: дадена мрежа
    :type network: list(list(dict(str, list)))
    :param row: една инстанца на податоци
    :type row: list
    :param l_rate: рата на учење
    :type l_rate: float
    :return: None
    """
    for i in range(len(network)):
        inputs = row[:-1]
        if i != 0:
            inputs = [neuron['output'] for neuron in network[i - 1]]
        for neuron in network[i]:
            for j in range(len(inputs)):
                neuron['weights'][j] += l_rate * neuron['delta'] * inputs[j]
            neuron['weights'][-1] += l_rate * neuron['delta']


def train_network(network, train, l_rate, n_epoch, n_outputs, verbose=True):
    """Тренирање на мрежата за фиксен број на епохи

    :param network: дадена мрежа
    :type network: list(list(dict(str, list)))
    :param train: тренирачко множество
    :type train: list
    :param l_rate: рата на учење
    :type l_rate: float
    :param n_epoch: број на епохи
    :type n_epoch: int
    :param n_outputs: број на неврони (класи) во излезниот слој
    :type n_outputs: int
    :param verbose: True за принтање на лог, инаку False
    :type: verbose: bool
    :return: None
    """
    for epoch in range(n_epoch):
        sum_error = 0
        for row in train:
            outputs = forward_propagate(network, row)
            expected = [0] * n_outputs
            expected[row[-1]] = 1
            sum_error += sum([(expected[i] - outputs[i]) ** 2 for i in range(len(expected))])
            backward_propagate_error(network, expected)
            update_weights(network, row, l_rate)
        if verbose:
            print('>epoch=%d, lrate=%.3f, error=%.3f' % (epoch, l_rate, sum_error))


def predict(network, row):
    """Направи предвидување

    :param network: дадена мрежа
    :type network: list(list(dict(str, list)))
    :param row: една податочна инстанца
    :type row: list
    :return: предвидени класи
    """
    outputs = forward_propagate(network, row)
    return outputs.index(max(outputs))


dataset = [[-0.25373134328358204, 0.5652173913043477, -0.4280788177339901, 0.4875, 0.5399999999999994, 0],
           [0.3731343283582091, 0.5, -0.4766734279918865, 0.625, 1.0, 0],
           [-0.11940298507462675, 0.5061728395061729, -0.5091025915613623, 0.6630434782608701, 1.0, 0],
           [0.7313432835820894, 0.5833333333333333, -0.6284306826178747, 0.8214285714285718, -0.7523809523809535, 0],
           [0.05970149253731361, 0.5698924731182795, -0.7504105090311989, 0.5740740740740742, 0.3185185185185191, 0],
           [0.4626865671641791, 0.393939393939394, -0.4302134646962229, 0.8888888888888891, 1.0, 0],
           [-0.7462686567164178, 0.393939393939394, -0.7290640394088669, 0.41666666666666696, 0.4888888888888882, 1],
           [-0.11940298507462675, 0.8611111111111112, -0.7763975155279502, 0.8478260869565221, -1.0, 1],
           [-0.6567164179104478, 0.2857142857142856, -0.16435288849081894, 0.3522727272727275, 1.0, 1],
           [0.28358208955223896, 0.4736842105263157, -0.16871921182266006, 0.5937500000000002, 1.0, 0],
           [-0.16417910447761186, 0.7222222222222221, -0.4088669950738916, 0.7386363636363638, 1.0, 1],
           [-0.6119402985074627, 0.16666666666666674, -0.2487684729064035, 0.41666666666666696, 0.2333333333333325, 1],
           [-0.07462686567164167, 0.5238095238095237, -0.4889162561576354, 0.6822916666666667, 0.6166666666666667, 0],
           [-0.16417910447761186, 0.4871794871794872, -0.5136587550380649, 0.3522727272727275, 1.0, 1],
           [-0.4328358208955224, 0.3333333333333335, -0.480911330049261, 0.5937500000000002, -0.1500000000000008, 1],
           [0.3731343283582091, 0.8148148148148147, -0.3184584178498988, 0.8750000000000002, 1.0, 0],
           [-0.29850746268656714, 0.6825396825396826, -0.4897588799585165, 0.5657894736842108, 0.5157894736842108, 0],
           [0.28358208955223896, 0.20634920634920628, -0.4568965517241379, 0.7265625000000002, 1.0, 0],
           [-0.4776119402985075, 0.44444444444444464, -0.2807881773399016, 0.41666666666666696, 1.0, 1],
           [0.28358208955223896, 0.3333333333333335, -0.312807881773399, 0.5937500000000002, 0.4249999999999996, 0],
           [-0.46268656716417894, 0.6153846153846152, -0.943456843007068, 0.4782608695652175, 1.0, 1],
           [-0.20895522388059692, 0.4666666666666666, -0.20760028149190712, 0.7202380952380956, -0.3142857142857156, 1],
           [-0.5671641791044777, 0.5555555555555556, -0.3497536945812809, 0.961538461538462, 1.0, 1],
           [-0.07462686567164167, 0.7435897435897441, -0.6330049261083743, 0.9479166666666669, 1.0, 0],
           [-0.4776119402985075, 0.44444444444444464, -0.4088669950738916, 0.7000000000000004, -0.22666666666666724, 0],
           [0.1940298507462688, 0.29824561403508776, -0.30640394088669953, 0.5583333333333336, 1.0, 1],
           [0.28358208955223896, 0.4736842105263157, -0.7450738916256158, 0.8593750000000002, 0.4249999999999996, 1],
           [-0.4776119402985075, 0.04761904761904767, -0.3320197044334974, 0.841666666666667, 1.0, 1],
           [-0.16417910447761186, 0.6000000000000001, -0.3390058217644425, 0.7386363636363638, 0.581818181818182, 1],
           [-0.07462686567164167, 0.5238095238095237, -0.5049261083743842, 0.2395833333333333, 1.0, 0]]

if __name__ == "__main__":
    seed(1)

    n_inputs = len(dataset[0]) - 1
    n_outputs = len(set([row[-1] for row in dataset]))

    n_hidden = int(input())
    l_rate = float(input())
    n_epoch = int(input())
    percent = float(input())

    size = int(len(dataset) * (1 - percent))
    training_set = dataset[:size]
    validation_set = dataset[size:]

    network = initialize_network(n_inputs, n_hidden, n_outputs)
    train_network(network, training_set, l_rate, n_epoch, n_outputs, False)

    correct = 0
    for sample in validation_set:
        if predict(network, sample) == sample[-1]:
            correct += 1

    tocni = correct / len(validation_set)
    print("Tochnost so site karakteristiki: " + str(round(tocni, 4)))

    pad = -999999
    karakteristika = None
    for i in range(n_inputs):
        temp_training_set = []
        for sample in training_set:
            temp_training_set.append(sample[:i] + sample[i + 1:])
        temp_validation_set = []
        for sample in validation_set:
            temp_validation_set.append(sample[:i] + sample[i + 1:])

        network_temp = initialize_network(n_inputs - 1, n_hidden, n_outputs)
        train_network(network_temp, temp_training_set, l_rate, n_epoch, n_outputs, False)

        correct = 0
        for sample in temp_validation_set:
            if predict(network_temp, sample) == sample[-1]:
                correct += 1

        tocni_temp = correct / len(temp_validation_set)
        pad_temp = tocni - tocni_temp

        if pad_temp > pad:
            pad = pad_temp
            karakteristika = i + 1

    print("Najgolem pad na tochnost: " + str(round(pad, 4)))
    print("Najvazhna karakteristika: " + str(karakteristika))