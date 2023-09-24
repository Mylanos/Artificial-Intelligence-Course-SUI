#!/usr/bin/env python
# coding: utf-8

# Vítejte u druhého projektu do SUI.
# V rámci projektu Vás čeká několik cvičení, v nichž budete doplňovat poměrně malé fragmenty kódu (místo je vyznačeno pomocí `None` nebo `pass`).
# Pokud se v buňce s kódem již něco nachází, využijte/neničte to.
# Buňky nerušte ani nepřidávejte.
# 
# Až budete s řešením hotovi, vyexportujte ho ("Download as") jako PDF i pythonovský skript a ty odevzdejte pojmenované názvem týmu (tj. loginem vedoucího).
# Dbejte, aby bylo v PDF všechno vidět (nezůstal kód za okrajem stránky apod.).
# 
# U všech cvičení je uveden orientační počet řádků řešení.
# Berte ho prosím opravdu jako orientační, pozornost mu věnujte, pouze pokud ho významně překračujete.

# In[1]:


import numpy as np
import copy
import matplotlib.pyplot as plt
import scipy.stats


# # Přípravné práce
# Prvním úkolem v tomto projektu je načíst data, s nimiž budete pracovat.
# Vybudujte jednoduchou třídu, která se umí zkonstruovat z cesty k negativním a pozitivním příkladům, a bude poskytovat:
# - pozitivní a negativní příklady (`dataset.pos`, `dataset.neg` o rozměrech [N, 7])
# - všechny příklady a odpovídající třídy (`dataset.xs` o rozměru [N, 7], `dataset.targets` o rozměru [N])
# 
# K načítání dat doporučujeme využít `np.loadtxt()`.
# Netrapte se se zapouzdřováním a gettery, berte třídu jako Plain Old Data.
# 
# Načtěte trénovací (`{positives,negatives}.trn`), validační (`{positives,negatives}.val`) a testovací (`{positives,negatives}.tst`) dataset, pojmenujte je po řadě `train_dataset`, `val_dataset` a `test_dataset`. 
# 
# **(6 řádků)** 
# 

# In[2]:


class BinaryDataset:
    def __init__(self, pos_ds, neg_ds):
        self.pos = np.loadtxt(pos_ds)
        self.neg = np.loadtxt(neg_ds)
        self.xs = np.concatenate((self.pos, self.neg))
        self.targets = np.concatenate((np.ones(len(self.pos)), np.zeros(len(self.neg))))

train_dataset = BinaryDataset('positives.trn', 'negatives.trn')
val_dataset = BinaryDataset('positives.val', 'negatives.val')
test_dataset = BinaryDataset('positives.tst', 'negatives.tst')

print('positives', train_dataset.pos.shape)
print('negatives', train_dataset.neg.shape)
print('xs', train_dataset.xs.shape)
print('targets', train_dataset.targets.shape)


# V řadě následujících cvičení budete pracovat s jedním konkrétním příznakem. Naimplementujte proto funkci, která vykreslí histogram rozložení pozitivních a negativních příkladů z jedné sady. Nezapomeňte na legendu, ať je v grafu jasné, které jsou které. Funkci zavoláte dvakrát, vykreslete histogram příznaku `5` -- tzn. šestého ze sedmi -- pro trénovací a validační data
# 
# **(5 řádků)**

# In[3]:


FOI = 5  # Feature Of Interest

def plot_data(poss, negs):
    plt.hist(poss, bins=25, color='g', label='Positives', histtype='step')
    plt.hist(negs, bins=25, color='r', label='Negatives', histtype='step')
    plt.legend()
    plt.ylabel('Number of samples')
    plt.xlabel('Value of the feature')
    plt.show()
    
plot_data(train_dataset.pos[:, FOI], train_dataset.neg[:, FOI])
plot_data(val_dataset.pos[:, FOI], val_dataset.neg[:, FOI])


# ### Evaluace klasifikátorů
# Než přistoupíte k tvorbě jednotlivých klasifikátorů, vytvořte funkci pro jejich vyhodnocování.
# Nechť se jmenuje `evaluate` a přijímá po řadě klasifikátor, pole dat (o rozměrech [N, F]) a pole tříd ([N]).
# Jejím výstupem bude _přesnost_ (accuracy), tzn. podíl správně klasifikovaných příkladů.
# 
# Předpokládejte, že klasifikátor poskytuje metodu `.prob_class_1(data)`, která vrací pole posteriorních pravděpodobností třídy 1 pro daná data.
# Evaluační funkce bude muset provést tvrdé prahování (na hodnotě 0.5) těchto pravděpodobností a srovnání získaných rozhodnutí s referenčními třídami.
# Využijte fakt, že `numpy`ovská pole lze mj. porovnávat se skalárem.
# 
# **(3 řádky)**

# In[4]:


def evaluate(classifier, inputs, targets):
    preds = classifier.prob_class_1(inputs)
    correct = np.abs(preds - targets) < 0.5
    return np.mean(correct)
    
class Dummy:
    def prob_class_1(self, xs):
        return np.asarray([0.2, 0.7, 0.7])

print(evaluate(Dummy(), None, np.asarray([0, 0, 1])))  # should be 0.66


# ### Baseline
# Vytvořte klasifikátor, který ignoruje vstupní data.
# Jenom v konstruktoru dostane třídu, kterou má dávat jako tip pro libovolný vstup.
# Nezapomeňte, že jeho metoda `.prob_class_1(data)` musí vracet pole správné velikosti.
# 
# **(4 řádky)**

# In[5]:


class PriorClassifier:
    def __init__(self, tip_class):
        self.tip_class = tip_class
        
    def prob_class_1(self, xs):
        return np.full(len(xs), self.tip_class)
        

baseline = PriorClassifier(0)
val_acc = evaluate(baseline, val_dataset.xs[:, FOI], val_dataset.targets)
print('Baseline val acc:', val_acc)


# # Generativní klasifikátory
# V této  části vytvoříte dva generativní klasifikátory, oba založené na Gaussovu rozložení pravděpodobnosti.
# 
# Začněte implementací funce, která pro daná 1-D data vrátí Maximum Likelihood odhad střední hodnoty a směrodatné odchylky Gaussova rozložení, které data modeluje.
# Funkci využijte pro natrénovaní dvou modelů: pozitivních a negativních příkladů.
# Získané parametry -- tzn. střední hodnoty a směrodatné odchylky -- vypíšete.
# 
# **(1 řádek)**

# In[6]:


def mle_gauss_1d(data):
    return np.mean(data), np.std(data)

mu_pos, std_pos = mle_gauss_1d(train_dataset.pos[:, FOI])
mu_neg, std_neg = mle_gauss_1d(train_dataset.neg[:, FOI])

print('Pos mean: {:.2f} std: {:.2f}'.format(mu_pos, std_pos))
print('Neg mean: {:.2f} std: {:.2f}'.format(mu_neg, std_neg))


# Ze získaných parametrů vytvořte `scipy`ovská gaussovská rozložení `scipy.stats.norm`.
# S využitím jejich metody `.pdf()` vytvořte graf, v němž srovnáte skutečné a modelové rozložení pozitivních a negativních příkladů.
# Rozsah x-ové osy volte od -0.5 do 1.5 (využijte `np.linspace`) a u volání `plt.hist()` nezapomeňte nastavit `density=True`, aby byl histogram normalizovaný a dal se srovnávat s modelem.
# 
# **(2 + 8 řádků)**

# In[7]:


ls = np.linspace(-0.5, 1.5, 100)

norm_pos = scipy.stats.norm(loc=mu_pos, scale=std_pos)
plt.plot(ls, norm_pos.pdf(ls), label='N('+str(np.round(mu_pos,4))+', '+str(np.round(std_pos*std_pos,4))+')')
plt.hist(train_dataset.pos[:, FOI] , bins=25, color='g', label='Positives', histtype='step', density=True)
plt.legend()
plt.xlabel('x')
plt.ylabel('p(x)')
plt.show()

norm_neg = scipy.stats.norm(loc=mu_neg, scale=std_neg)
plt.plot(ls, norm_neg.pdf(ls), label='N('+str(np.round(mu_neg,4))+', '+str(np.round(std_neg*std_neg,4))+')')
plt.hist(train_dataset.neg[:, FOI], bins=25, color='r', label='Negatives', histtype='step', density=True)
plt.legend()
plt.xlabel('x')
plt.ylabel('p(x)')
plt.show()

pass


# Naimplementujte binární generativní klasifikátor. 
# Při konstrukci přijímá dvě rozložení poskytující metodu `.pdf()` a odpovídající apriorní pravděpodobnost tříd.
# Dbejte, aby Vám uživatel nemohl zadat neplatné apriorní pravděpodobnosti.
# Jako všechny klasifikátory v tomto projektu poskytuje metodu `prob_class_1()`.
# 
# **(9 řádků)**

# In[8]:


class GenerativeClassifier2Class:
    def __init__(self, dist_pos, dist_neg, apr_pos):
        assert 0 <= apr_pos and apr_pos <= 1
        self.dist_pos = dist_pos
        self.dist_neg = dist_neg
        self.apr_pos = apr_pos
         
    def prob_class_1(self, xs):
        probs_pos = []
        for sample in xs:
            prob_pos = self.dist_pos.pdf(sample) * self.apr_pos
            prob_pos /= prob_pos + self.dist_neg.pdf(sample) * (1.0 - self.apr_pos)
            probs_pos.append(prob_pos)
        return np.array(probs_pos)


# Nainstancujte dva generativní klasifikátory: jeden s rovnoměrnými priory a jeden s apriorní pravděpodobností 0.75 pro třídu 0 (negativní příklady).
# Pomocí funkce `evaluate()` vyhodnotíte jejich úspěšnost na validačních datech.
# 
# **(2 řádky)**

# In[9]:


classifier_flat_prior = GenerativeClassifier2Class(norm_pos, norm_neg, 0.5)
classifier_full_prior = GenerativeClassifier2Class(norm_pos, norm_neg, (1.0 - 0.75))


print('flat:', evaluate(classifier_flat_prior, val_dataset.xs[:, FOI], val_dataset.targets))
print('full:', evaluate(classifier_full_prior, val_dataset.xs[:, FOI], val_dataset.targets))


# Vykreslete průběh posteriorní pravděpodobnosti třídy 1 jako funkci příznaku 5, opět v rozsahu <-0.5; 1.5> pro oba klasifikátory.
# Do grafu zakreslete i histogramy rozložení trénovacích dat, opět s `density=True` pro zachování dynamického rozsahu.
# 
# **(8 řádků)**

# In[18]:


plt.hist(train_dataset.pos[:, FOI], color='g', bins=15, label='Training data positive', histtype='step', density=True, range=[-0.5, 1.5])
plt.hist(train_dataset.neg[:, FOI], color='r', bins=15, label='Training data negative', histtype='step', density=True)

vxs = np.linspace(-0.5, 1.5, num=50)
plt.plot(vxs, classifier_flat_prior.prob_class_1(vxs), c='b', label='Flat posterior positive')
plt.plot(vxs, classifier_full_prior.prob_class_1(vxs), c='k', label='Full posterior positive')

plt.xlabel('Feature_5')
plt.ylabel('P(class_1)')
plt.legend()
plt.show()


# # Diskriminativní klasifikátory
# V následující části budete pomocí (lineární) logistické regrese přímo modelovat posteriorní pravděpodobnost třídy 1.
# Modely budou založeny čistě na NumPy, takže nemusíte instalovat nic dalšího.
# Nabitějších toolkitů se dočkáte ve třetím projektu.

# In[19]:


def logistic_sigmoid(x):
    return np.exp(-np.logaddexp(0, -x))

def binary_cross_entropy(probs, targets):
    return np.sum(-targets * np.log(probs) - (1-targets)*np.log(1-probs)) 

class LogisticRegressionNumpy:
    def __init__(self, dim):
        self.w = np.array([0.0] * dim)
        self.b = np.array([0.0])
        
    def prob_class_1(self, x):
        return logistic_sigmoid(x @ self.w + self.b)


# Diskriminativní klasifikátor očekává, že dostane vstup ve tvaru `[N, F]`.
# Pro práci na jediném příznaku bude tedy zapotřebí vyřezávat příslušná data v správném formátu (`[N, 1]`). 
# Doimplementujte třídu `FeatureCutter` tak, aby to zařizovalo volání její instance.
# Který příznak se použije, nechť je konfigurováno při konstrukci.
# 
# Může se Vám hodit `np.newaxis`.
# 
# **(2 řádky)**

# In[20]:


class FeatureCutter:
    def __init__(self, fea_id):
        self.fea_id = fea_id
        
    def __call__(self, x):
        return x[:, self.fea_id, np.newaxis]


# Dalším krokem je implementovat funkci, která model vytvoří a natrénuje.
# Jejím výstupem bude (1) natrénovaný model, (2) průběh trénovací loss a (3) průběh validační přesnosti.
# Neuvažujte žádné minibatche, aktualizujte váhy vždy na celém trénovacím datasetu.
# Po každém kroku vyhodnoťte model na validačních datech.
# Jako model vracejte ten, který dosáhne nejlepší validační přesnosti.
# Jako loss použijte binární cross-entropii  a logujte průměr na vzorek.
# Pro výpočet validační přesnosti využijte funkci `evaluate()`.
# Oba průběhy vracejte jako obyčejné seznamy.
# 
# Doporučujeme dělit efektivní learning rate počtem vzorků, na nichž je počítana loss.
# 
# **(cca 11 řádků)**

# In[21]:


def train_logistic_regression(nb_epochs, lr, in_dim, fea_preprocessor):
    model = LogisticRegressionNumpy(in_dim)
    best_model = copy.deepcopy(model)
    losses = []
    accuracies = []
    
    train_X = fea_preprocessor(train_dataset.xs)
    train_t = train_dataset.targets
    val_X = fea_preprocessor(val_dataset.xs)
    val_t = val_dataset.targets
    lr /= len(train_X)
    
    for i in range(nb_epochs):
        preds = model.prob_class_1(train_X)
        loss = binary_cross_entropy(preds, train_t)
        losses.append(loss)
                
        diff = preds - train_t
        gradient_b = np.sum(diff)
        gradients_w = np.matmul(train_X.transpose(), diff)
        gradients_w = np.array([np.mean(grad) for grad in gradients_w])
        model.w -= lr * gradients_w
        model.b -= lr * gradient_b
            
        accuracy = evaluate(model, val_X, val_t)
        accuracies.append(accuracy)
        if i > 0:
            if accuracy < accuracies[i-1]:
                best_model = copy.deepcopy(model)
        
    return best_model, losses, accuracies


# Funkci zavolejte a natrénujte model.
# Uveďte zde parametry, které vám dají slušný výsledek.
# Měli byste dostat přesnost srovnatelnou s generativním klasifikátorem s nastavenými priory.
# Neměli byste potřebovat víc, než 100 epoch.
# Vykreslete průběh trénovací loss a validační přesnosti, osu x značte v epochách.
# 
# V druhém grafu vykreslete histogramy trénovacích dat a pravděpodobnost třídy 1 pro x od -0.5 do 1.5, podobně jako výše u generativních klasifikátorů.
# 
# **(1 + 5 + 8 řádků)**

# In[22]:


disc_fea5, losses, accuracies = train_logistic_regression(100, 9, 1, FeatureCutter(FOI))

_, axs = plt.subplots(1, 2)
axs[0].plot(range(1,len(losses)+1), losses, label='Loss', color='r')
axs[1].plot(range(1,len(accuracies)+1), accuracies, label='Accuracy')
plt.xlabel("Epoch")
plt.legend()
plt.show()
print('w', disc_fea5.w.item(), 'b', disc_fea5.b.item())

plt.hist(train_dataset.pos[:, FOI], color='g', bins=25, label='Training data positive', histtype='step', density=True, range=[-0.5, 1.5])
plt.hist(train_dataset.neg[:, FOI], color='r', bins=25, label='Training data negative', histtype='step', density=True)
vxs = np.linspace(-0.5, 1.5, num=50)
plt.plot(vxs, disc_fea5.prob_class_1(vxs[:, np.newaxis]).squeeze(), c='b', label='P(class_1)')
plt.legend()
plt.show()
print('disc_fea5:', evaluate(disc_fea5, val_dataset.xs[:, FOI][:, np.newaxis], val_dataset.targets))


# ## Všechny vstupní příznaky
# V posledním cvičení natrénujete logistickou regresi, která využije všechn sedm vstupních příznaků.
# Zavolejte funkci z předchozího cvičení, opět vykreslete průběh trénovací loss a validační přesnosti.
# Měli byste se dostat nad 90 % přesnosti.
# 
# Může se Vám hodit `lambda` funkce.
# 
# **(1 + 5 řádků)**

# In[23]:


disc_full_fea, losses, accuracies = train_logistic_regression(100, 0.007, train_dataset.xs.shape[1], lambda x : x)

_, axs = plt.subplots(1, 2)
axs[0].plot(range(1,len(losses)+1), losses, label='Loss', color='r')
axs[1].plot(range(1,len(accuracies)+1), accuracies, label='Accuracy')
plt.xlabel("Epoch")
plt.legend()
plt.show()


# # Závěrem
# Konečně vyhodnoťte všech pět vytvořených klasifikátorů na testovacích datech.
# Stačí doplnit jejich názvy a předat jim odpovídající příznaky.
# Nezapomeňte, že u logistické regrese musíte zopakovat formátovací krok z `FeatureCutter`u.

# In[24]:


xs_full = test_dataset.xs
xs_foi = test_dataset.xs[:, FOI]
targets = test_dataset.targets

print('Baseline:', evaluate(baseline, xs_full, targets))
print('Generative classifier (w/o prior):', evaluate(classifier_flat_prior, xs_foi, targets))
print('Generative classifier (correct):', evaluate(classifier_full_prior, xs_foi, targets))
print('Logistic regression:', evaluate(disc_fea5, xs_foi[:, np.newaxis], targets))
print('logistic regression all features:', evaluate(disc_full_fea, xs_full, targets))


# Blahopřejeme ke zvládnutí projektu! Nezapomeňte spustit celý notebook načisto (Kernel -> Restart & Run all) a zkontrolovat, že všechny výpočty prošly podle očekávání.
# 
# Mimochodem, vstupní data nejsou synteticky generovaná.
# Nasbírali jsme je z baseline řešení předloňského projektu; vaše klasifikátory v tomto projektu predikují, že daný hráč vyhraje dicewars, takže by se daly použít jako heuristika pro ohodnocování listových uzlů ve stavovém prostoru hry.
# Pro představu, data jsou z pozic pět kol před koncem partie pro daného hráče.
# Poskytnuté příznaky popisují globální charakteristiky stavu hry jako je například poměr délky hranic předmětného hráče k ostatním hranicím.
# Nejeden projekt v ročníku 2020 realizoval požadované "strojové učení" kopií domácí úlohy.

# In[ ]:





# In[ ]:





# In[ ]:





# In[ ]:





# In[ ]:





# In[ ]:




