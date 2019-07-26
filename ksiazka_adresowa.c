/* autor: Pawel Ostaszewski numer indeksu 273888 */

#include <stdio.h>
#include <stdbool.h>
#include <string.h>
#include <ctype.h>
#include <stdlib.h>
#include <limits.h>
#include <math.h>
#include <time.h>

/* procedury (makra) wykorzystywane w kolejce priorytetowej */
#define PRZODEK(i) (int)floor((i-1)/2)
#define LEWY(i) 2*i+1
#define PRAWY(i) 2*i+2

/************************** struktury podstawowe ******************************/

typedef struct
{
  char ulica[32];
  int nr_domu;
  int nr_mieszkania;
  char kod_pocztowy[7]; // 01-234 przechowujemy jako "01-234"
  char miasto[32];      // zakonczone znakiem '\0'
} adres;

/* reprezentacja osoby w bazie - grafie */
typedef struct wezel
{
  /* identyfikator osoby - klucz wezla */
  int id;
  /* atrybuty podstawowe */
  char pierwsze_imie[32];
  char drugie_imie[32];
  char nazwisko[32];
  adres adres;
  int nr_telefonu;
  /* atrybuty wykorzystywane do utrzymania struktury grafu */
  struct wezel *nastepny; /* wskaznik do nastepnego wezla w liscie wszystkich wezlow grafu */
  struct krawedz *pierwszy; /* pierwsza znajomosc w liscie znajomych osob */
  /* atrybuty wykorzystywane w algorytmie Dijkstry  */
  struct wezel* poprzednik;
  int odleglosc;
  int liczba_krawedzi; /* liczba krawedzi dzielacych dany wezel */
} wezel;              /* od wezla zrodlowego w najlepszej sciezce */

/* krawedz miedzy wezlami - odpowiednik znajomosci miedzy osobami
   wykorzystujac ponizsza strukture mozemy stworzyc
   dynamiczna liste znajomosci danej osoby */
typedef struct krawedz
{
  wezel *cel; /* wskaznik do wezla do ktorego prowadzi dana krawedz (osoba z ktora ktos zawarl znajomosc) */
  short waga; /* stopien znajomosci z osoba do ktorej prowadzi krawedz (skala od 1 do 10) */
  struct krawedz *nastepny; /* nastepna znajomosc danej osoby w liscie znajomosci */
} krawedz;

/* graf jest dynamiczna lista wszystkich wezlow. Kazdy wezel posiada liste wezlow, */
/* ktore sa z nim polaczone krawedzia, tzn. kazda osoba posiada liste swoich znajomych */
/* do grafu odwolujemy sie za pomoca wskaznika zrodlo */
typedef struct baza
{
  wezel *zrodlo; /* pierwszy wezel w liscie wszystkich wezlow grafu */
  int liczba_elementow;
  int biezacy_id;
} baza; /* baza - graf - ksiazka adresowo-spolecznosciowa */

/* tworzymy dwie nazwy dla tej samej struktury, zeby latwiej bylo zrozumiec */
/* kiedy poslugujemy sie baza jako grafem, a kiedy jako ksiazka adresowa  */
typedef baza graf;

void inicjalizacja_bazy(baza *b)
{
  b->liczba_elementow = 0;
  b->biezacy_id = 1; /* id zwiekszamy o jeden po dodaniu kazdej nowej osoby */
  b->zrodlo = NULL;
}

/************************ algorytm Dijkstry *******************************/

/* kolejka priorytetowa zaimplementowana jako kopiec binarny typu min */
/* (podobnie jak w ksiazce Cormena rozdzial 6 - Heapsort) */
typedef struct
{
  wezel **tablica; /* tablica wskaznikow do wszystkich wezlow grafu */
  int rozmiar;
} kopiec_min;

/* przywracanie struktury kopca binarnego, ktora zostala zaburzona */
/* indeks i wskazuje na wezel w kopcu ktory moze miec wieksza odleglosc */
/* od zrodla niz wezly z lewego i prawego poddrzewa */
/* funkcja analogiczna do funkcji max_heapify z ksiazki Cormena */
void przywracanie_kopca(kopiec_min *kopiec, int i)
{
  int lewy, prawy, najmniejszy;
  wezel *temp;
  lewy = LEWY(i); /* indeks w tablicy lewego potomka elementu o indeksie i */
  prawy = PRAWY(i); /* indeks w tablicy prawego potomka elementu o indeksie i */
  if(lewy <= kopiec->rozmiar-1 && kopiec->tablica[lewy]->odleglosc < kopiec->tablica[i]->odleglosc)
    najmniejszy = lewy;
  else
    najmniejszy = i;
  if(prawy <= kopiec->rozmiar-1 && kopiec->tablica[prawy]->odleglosc < kopiec->tablica[najmniejszy]->odleglosc)
    najmniejszy = prawy;
  if(najmniejszy != i)
  {
    /* zamiana wskaznikow */
    temp = kopiec->tablica[i];
    kopiec->tablica[i] = kopiec->tablica[najmniejszy];
    kopiec->tablica[najmniejszy] = temp;
    przywracanie_kopca(kopiec, najmniejszy);
  }
}

/* n - liczba osob (wezlow) w bazie
   wezelwsk - wskaznik na pierwszy wezel w liscie wszystkich wezlow grafu
   zrodlo - wskaznik na wezel z ktorego zaczynamy poszukiwanie sciezki w algorytmie Dijkstry */
/* funkcja analogiczna do funkcji build_max_heap z ksiazki Cormena */
void budowanie_kopca(kopiec_min *kopiec, wezel *wezelwsk, wezel* zrodlo, int n)
{
  int i;

  kopiec->rozmiar = n;
  kopiec->tablica = (wezel**) malloc(n*sizeof(wezel*));

  for(i = 0; i < n; i++)
  {
    kopiec->tablica[i] = wezelwsk;
    kopiec->tablica[i]->poprzednik = NULL;
    if(wezelwsk == zrodlo)
    {
      kopiec->tablica[i]->odleglosc = 0;
      kopiec->tablica[i]->liczba_krawedzi = 0;
    }
    else /* za pomoca INT_MAX oznaczamy ze dany wezel jest nieosiagalny z wezla zrodlowego */
      kopiec->tablica[i]->odleglosc = INT_MAX;
    wezelwsk = wezelwsk->nastepny;
  }

  for(i = (int)floor(kopiec->rozmiar/2); i >= 0; i--)
    przywracanie_kopca(kopiec, i);
}

/* funkcja pozwalajaca na wprowadzenie nowej odleglosci do elementu kopca */
/* (odleglosci od wezla zrodlowego) przy zachowaniu struktury kopca binarnego */
/* jesli nowa odleglosc nie jest mniejsza od dotychczasowej odleglosci od zrodla */
/* to funkcja zwraca -1 (bedziemy zmniejszac odleglosci w algorytmie Dijkstry)  */
/* funkcja analogiczna do funkcji heap_increase_key z ksiazki Cormena */
int zmniejsz_odleglosc(kopiec_min *kopiec, wezel *zmieniany, int nowa_odleglosc)
{
  wezel *temp;
  int i;

  for(i = 0; i < kopiec->rozmiar; i++)
  {/* zakladamy ze wskaznik zmieniany pokazuje na wezel ktory istnieje w grafie */
    if(kopiec->tablica[i] == zmieniany)
      break;
  }
  if(nowa_odleglosc > kopiec->tablica[i]->odleglosc)
    return -1;
  kopiec->tablica[i]->odleglosc = nowa_odleglosc;
  while(i > 0 && kopiec->tablica[PRZODEK(i)]->odleglosc > kopiec->tablica[i]->odleglosc)
  {
    /* zamiana wskaznikow */
    temp = kopiec->tablica[i];
    kopiec->tablica[i] = kopiec->tablica[PRZODEK(i)];
    kopiec->tablica[PRZODEK(i)] = temp;
    i = PRZODEK(i);
  }
  return 0;
}

/* funkcja zwracajaca wezel o najmniejszej odleglosci od zrodla (zlozonosc O(1)) */
/* jesli kopiec pusty to funkcja zwraca NULL */
/* funkcja analogiczna do funkcji exrtract_max z ksiazki Cormena */
wezel* pobierz_minimalny(kopiec_min *kopiec)
{
  wezel* min;
  if(kopiec->rozmiar < 1) return NULL; /* kopiec pusty */
  min = kopiec->tablica[0];
  kopiec->tablica[0] = kopiec->tablica[kopiec->rozmiar-1];
  kopiec->rozmiar--;
  przywracanie_kopca(kopiec, 0);
  return min;
}

/* jesli tryb == 1 to wyszukiwanie najszybszej sciezki, jesli tryb == 2 */
/* to wyszukiwanie najskuteczniejszej sciezki */
/* zrodlo i cel to wskazniki na wezly miedzy ktorymi szukamy najlepszej sciezki */
/* zakladamy ze te wezly istnieja w grafie */
/* jesli nie istnieje sciezka miedzy dwoma wezlami to funkcja zwraca NULL */
/* w przeciwnym przypadku funkcja zwraca wskaznik do wezla cel, z ktorego mozemy */
/* odtworzyc sciezke za pomoca zmiennej skladowej wezla "poprzednik" */
wezel* algorytm_dijkstry(graf *g, wezel *zrodlo, wezel *cel, int tryb)
{
  kopiec_min kopiec;
  wezel *min;
  krawedz *sasiad; /* wskaznik na sasiada wezla min */

/* b.zrodlo - wskaznik na pierwszy wezel w liscie wezlow, zrodlo - opis powyzej */
  budowanie_kopca(&kopiec, g->zrodlo, zrodlo, g->liczba_elementow);

  while(kopiec.rozmiar > 0)
  {
    min = pobierz_minimalny(&kopiec);

    /* jesli wezel o najmniejszej odleglosci od zrodla ma odleglosc rowna INT_MAX tzn. nieskonczonosc */
    /* to znaczy ze wszystkie wezly do ktorych mozna dojsc z wezla zrodlowego zostaly juz przejrzane */
    /* Innymi slowy opuscilismy spojna skladowa grafu zawierajaca wezel zrodlowy */
    if(min->odleglosc == INT_MAX) /* wiec nie ma sensu poszukiwac dalej najkrotszej sciezki */
      break;

    sasiad = min->pierwszy; /* przechodzimy po liscie znajomych wezla min */
    while(sasiad != NULL)
    {
      if(tryb == 1)
      {
        if(min->odleglosc+1 < sasiad->cel->odleglosc)
        {
          zmniejsz_odleglosc(&kopiec, sasiad->cel, min->odleglosc+1);
          sasiad->cel->poprzednik = min;
        }
        if(sasiad->cel == cel)
        {
          free(kopiec.tablica);
          return cel;
        }
      }
      else /* tryb == 2 */
        if(min->odleglosc + (min->liczba_krawedzi+1)*(11-sasiad->waga)
           < sasiad->cel->odleglosc)
        {
          zmniejsz_odleglosc(&kopiec, sasiad->cel,
            min->odleglosc + (min->liczba_krawedzi+1)*(11-sasiad->waga));
          sasiad->cel->poprzednik = min;
          sasiad->cel->liczba_krawedzi = min->liczba_krawedzi+1;
        }
      sasiad = sasiad->nastepny;
    }
  }

  free(kopiec.tablica);
  if(cel->odleglosc < INT_MAX) /* jesli < INT_MAX to do wezla docelowego da sie dojsc z wezla zrodlowego */
    return cel;
  return NULL; /* przypadek gdy nie istnieje sciezka miedzy dwoma wezlami */
}

/*********************** operacje na grafie *******************************/

/* funkcja szuka w grafie wezla o identyfikatorze podanym jako argument
   jesli wezel o podanym id istnieje w grafie to funkcja zwraca wskaznik
   do tego wezla, w przeciwnym przypadku funkcja zwraca NULL */
wezel* znajdz_wezel(graf *g, int id)
{
  wezel *wezelwsk;

  if(g->zrodlo == NULL) /* przypadek gdy graf pusty */
    return NULL;
  if(g->zrodlo->id == id) /* przypadek gdy zrodlo jest szukanym wezlem */
    return g->zrodlo;

  wezelwsk = g->zrodlo; /* ogolny przypadek */
  while(wezelwsk->nastepny != NULL)
  {
    wezelwsk = wezelwsk->nastepny;
    if(wezelwsk->id == id)
      return wezelwsk;
  }
  return NULL;
}

/* Jesli nie istnieje krawedz miedzy wezlami o identyfikatorach */
/* id1, id2 to funkcja zwraca -1, w przeciwnym przypadku zwraca 0 */
int zmiana_wagi_krawedzi(graf *g, wezel *wezel1, wezel *wezel2, int nowa_waga)
{
  krawedz *krawedzwsk;

  krawedzwsk = wezel1->pierwszy;
  while(krawedzwsk != NULL)
  {
    if(krawedzwsk->cel == wezel2)
    {
      krawedzwsk->waga = nowa_waga;
      return 0;
    }
    krawedzwsk = krawedzwsk->nastepny;
  }
  return -1;
}

/* zakladamy ze wezel o podanym id nie istnieje w grafie */
/* funkcja zwraca wskaznik na nowo dodany wezel */
wezel* dodawanie_wezla(graf *g, int id)
{
  wezel *wezelwsk;
  wezel *nowy = (wezel*) malloc(sizeof(wezel));

  nowy->id = id;
  nowy->nastepny = NULL;
  nowy->pierwszy = NULL;

  if(g->zrodlo == NULL) /* graf pusty */
    g->zrodlo = nowy;
  else
  {
    wezelwsk = g->zrodlo;
    while(wezelwsk->nastepny != NULL)
      wezelwsk = wezelwsk->nastepny;
    wezelwsk->nastepny = nowy;
  }
  return nowy;
}

/* waga1 mowi w jakim stopniu osoba 1 zna osobe 2, waga2 odwrotnie */
/* Jesli waga1 lub waga2 nie miesci sie w przedziale [1, 10] */
/* to funkcja zwraca -1, jesli krawedz istniala juz wczesniej */
/* to funkcja zwraca -2, w przeciwnym przypadku funkcja zwraca 0 */
int dodawanie_krawedzi(graf *g, wezel *wezel1, wezel *wezel2, int waga1, int waga2)
{
  krawedz *nowa1, *nowa2;
  krawedz *krawedzwsk; /* wskaznik na dowolna krawedz */

  if(waga1 < 1 || 10 < waga1 || waga2 < 1 || 10 < waga2)
    return -1;

  nowa1 = (krawedz*) malloc(sizeof(krawedz));
  nowa2 = (krawedz*) malloc(sizeof(krawedz));

  nowa1->cel = wezel2;
  nowa2->cel = wezel1;
  nowa1->waga = waga1;
  nowa2->waga = waga2;
  nowa1->nastepny = NULL;
  nowa2->nastepny = NULL;

  krawedzwsk = wezel1->pierwszy;
  if(krawedzwsk == NULL) /* przypadek gdy pusta lista krawedzi */
    wezel1->pierwszy = nowa1;
  else if(krawedzwsk->cel == wezel2)
    return -2; /* krawedz zostala dodana juz wczesniej (pierwsza krawedz) */
  else
  {
    while(krawedzwsk->nastepny != NULL)
    {
      krawedzwsk = krawedzwsk->nastepny;
      if(krawedzwsk->cel == wezel2)
        return -2; /* krawedz zostala dodana juz wczesniej */
    }
    krawedzwsk->nastepny = nowa1;
  }

  krawedzwsk = wezel2->pierwszy;
  if(krawedzwsk == NULL) /* przypadek gdy pusta lista krawedzi */
    wezel2->pierwszy = nowa2;
  else /* tutaj juz nie trzeba sprawdzac czy istnieje krawedz, bo gdyby */
  { /* istniala to zostalaby wykryta przy przechodzeniu listy krawedzi */
    while(krawedzwsk->nastepny != NULL) /* wychodzacych od wezla1 */
      krawedzwsk = krawedzwsk->nastepny;
    krawedzwsk->nastepny = nowa2;
  }
  return 0;
}

/* rekurencyjne usuwanie wszystkich krawedzi wychodzacych wezla */
/* krawedzwsk na poczatku pokazuje na pierwsza krawedz z listy krawedzi wychodzacych */
void usuwanie_krawedzi_wychodzacych(krawedz *krawedzwsk)
{
  if(krawedzwsk == NULL)
    return ;
  usuwanie_krawedzi_wychodzacych(krawedzwsk->nastepny);
  free(krawedzwsk);
}

/* jesli nie istnieje krawedz z wezla zrodlowego do wezla docelowego */
/* to funkcja nie robic nic */
void usuwanie_krawedzi_wchodzacej(wezel *zrodlo, wezel *cel)
{
  krawedz *krawedzwsk, *temp;
  if(zrodlo->pierwszy == NULL)
    return ; /* przypadek gdy pusta lista krawedzi */

  /* przypadek gdy pierwsza krawedz wychodzaca wezla zrodlowego
  jest krawedzia wchodzaca wezla docelowego */
  if(zrodlo->pierwszy->cel == cel)
  {
    temp = zrodlo->pierwszy->nastepny;
    free(zrodlo->pierwszy);
    zrodlo->pierwszy = temp;
    return ;
  }
  /* przypadek ogolny */
  krawedzwsk = zrodlo->pierwszy;
  while(krawedzwsk->nastepny != NULL)
  {
    if(krawedzwsk->nastepny->cel == cel)
    {
      temp = krawedzwsk->nastepny->nastepny;
      free(krawedzwsk->nastepny);
      krawedzwsk->nastepny = temp;
      return ;
    }
    krawedzwsk = krawedzwsk->nastepny;
  }
}

/* usuwanie wezla razem ze wszystkimi krawedziami wchodzacymi i wychodzacymi */
/* jesli wezel o identyfikatorze id nie istnieje w grafie funkcja zwraca -1 */
/* w przeciwnym przypadku zwraca 0 */
int usuwanie_wezla(graf *g, int id)
{
  wezel *usuwany, *wezelwsk, *temp;
  bool usuniety = false;

  usuwany = znajdz_wezel(g, id);

  if(usuwany == NULL)
    return -1;

  usuwanie_krawedzi_wychodzacych(usuwany->pierwszy);
  usuwany->pierwszy = NULL;

  /* przypadek gdy usuwany wezel to pierwszy wezel grafu */
  if(g->zrodlo == usuwany)
  {
    temp = g->zrodlo->nastepny;
    free(g->zrodlo);
    g->zrodlo = temp;
    usuniety = true;
  }
  else
    usuwanie_krawedzi_wchodzacej(g->zrodlo, usuwany);

  wezelwsk = g->zrodlo;
  while(wezelwsk->nastepny != NULL)
  {
    if(!usuniety)
      if(wezelwsk->nastepny == usuwany)
      {
        temp = usuwany->nastepny;
        free(usuwany);
        wezelwsk->nastepny = temp;
        usuniety = true;
        continue;
      }
    wezelwsk = wezelwsk->nastepny;
    usuwanie_krawedzi_wchodzacej(wezelwsk, usuwany);
  }
  return 0;
}

/* ogolne usuwanie krawedzi miedzy dwoma wezlami */
/* funkcja zwraca -1 gdy w grafie nie istnieje ktorys z wezlow */
/* o identyfikatorach id1 lub id2. Jesli krawedz miedzy tymi wezlami */
/* nie istnieje to funkcja zwraca -2, w przeciwnym przypadku 0 */
int usuwanie_krawedzi(graf *g, int id1, int id2)
{
  wezel *wezel1, *wezel2;
  krawedz *krawedzwsk, *temp;
  bool istnieje_krawedz = false;

  wezel1 = znajdz_wezel(g, id1);
  wezel2 = znajdz_wezel(g, id2);

  if(wezel1 == NULL || wezel2 == NULL)
    return -1;

  krawedzwsk = wezel1->pierwszy;
  if(krawedzwsk == NULL) /* przypadek gdy pusta lista krawedzi */
    return -2;
  else if(krawedzwsk->cel->id == id2)
  {/* przypadek gdy szukana krawedz to pierwsza krawedz */
    temp = krawedzwsk->nastepny;
    free(krawedzwsk);
    wezel1->pierwszy = temp;
  }
  else
  {
    while(krawedzwsk->nastepny != NULL)
    {
      krawedzwsk = krawedzwsk->nastepny;
      if(krawedzwsk->cel->id == id2)
      {
        istnieje_krawedz = true;
        temp = krawedzwsk->nastepny;
        free(krawedzwsk);
        krawedzwsk = temp;
        break;
      }
    }
    if(!istnieje_krawedz)
      return -2;
  }

  /* tutaj mamy pewnosc ze szukana krawedz istnieje */
  krawedzwsk = wezel2->pierwszy;
  if(krawedzwsk->cel->id == id1)
  {/* przypadek gdy szukana krawedz to pierwsza krawedz */
    temp = krawedzwsk->nastepny;
    free(krawedzwsk);
    wezel2->pierwszy = temp;
  }
  else
  {/* przypadek gdy szukana krawedz nie jeste pierwsza krawedzia */
    while(krawedzwsk->nastepny != NULL)
    {
      krawedzwsk = krawedzwsk->nastepny;
      if(krawedzwsk->cel->id == id1)
      {
        temp = krawedzwsk->nastepny;
        free(krawedzwsk);
        krawedzwsk = temp;
        break;
      }
    }
  }
  return 0;
}

/* rekurencyjna funkcja uzywana w zwalnianiu pamieci calego grafu */
/* usuwane sa w niej tez wszystkie krawedzie */
/* wezelwsk na poczatku pokazuje na pierwszy wezel z listy wszystkich wezlow grafu */
void usuwanie_wszystkich_wezlow(wezel *wezelwsk)
{
  if(wezelwsk == NULL)
    return ;
  usuwanie_wszystkich_wezlow(wezelwsk->nastepny);
  usuwanie_krawedzi_wychodzacych(wezelwsk->pierwszy);
  free(wezelwsk);
}

/*************************** sortowanie ***********************************/

/* leksykograficzne sortowanie stringow */
/* nie zwracajace uwagi nie wielkosc liter (inaczej niz strcmp) */
/* dzieki temu sortowanie wedlug nazwisk wyglada w taki sposob: */
/* Glowacki kowalski Nowicki, zamiast: Glowacki Nowicki kowalski */
int string_compare(char* napis1, char* napis2)
{
  int i = 0;
  while(1)
  {
    if(napis1[i] == '\0' && napis2[i] == '\0') return 0;
    if(napis1[i] == '\0') return 1;
    if(napis2[i] == '\0') return -1;
    if(tolower(napis1[i]) > tolower(napis2[i])) return 1;
    if(tolower(napis2[i]) > tolower(napis1[i])) return -1;
    i++; /* tolower - funkcja z ctype.h */
  }
}

/* porownywanie zwracajace 1 gdy pierwszy element wiekszy od drugiego, -1 gdy pierwszy mniejszy */
/* od drugiego, 0 gdy sa rowne (tak samo jak biblioteczne funkcje porownujace np. strcmp) */
/* tryb == 1 - porownywanie identyfikatorow, tryb == 2 - porownywanie imion, tryb == 3 - porownywanie nazwisk */
int porownywanie(wezel *wsk1, wezel *wsk2, int tryb)
{
  if(tryb == 1)
  {
    if(wsk1->id > wsk2->id)
      return 1;
    else if(wsk1->id < wsk2->id)
      return -1;
    else return 0;
  }
  else
    return string_compare((tryb == 2)? wsk1->pierwsze_imie : wsk1->nazwisko,
                          (tryb == 2)? wsk2->pierwsze_imie : wsk2->nazwisko);
/* powyzej dwukrotnie zostalo uzyte wyrazenie warunkowe */
/* jesli tryb == 2 to porownywane sa imiona dwoch osob jesli tryb == 3 to nazwiska */
}

/* wsk1 jest wskaznikiem na wezly pierwszej listy, wsk2 na wezly drugiej */
/* na poczatku wsk1 i wsk2 pokazuja na pierwsze elementy obu list. wsk3 jest wskaznikiem na wezly */
/* posortowanej listy bedacej wynikiem scalenia obu list wskazywanych przez wsk1 i wsk2 */
/* funkcja zwraca wskaznik do pierwszego wezla posortowanej, scalonej listy */
wezel* scalanie_list(wezel *wsk1, wezel *wsk2, int tryb)
{
  wezel *wsk3;
  wezel *pierwszy;

  if(porownywanie(wsk1, wsk2, tryb) < 0)
  {
    pierwszy = wsk1;
    wsk1 = wsk1->nastepny;
  }
  else
  {
    pierwszy = wsk2;
    wsk2 = wsk2->nastepny;
  }
  wsk3 = pierwszy;
  while(wsk1 != NULL && wsk2 != NULL)
  {
    if(porownywanie(wsk1, wsk2, tryb) < 0)
    {
      wsk3->nastepny = wsk1;
      wsk3 = wsk3->nastepny;
      wsk1 = wsk1->nastepny;
    }
    else
    {
      wsk3->nastepny = wsk2;
      wsk3 = wsk3->nastepny;
      wsk2 = wsk2->nastepny;
    }
  }
  if(wsk1 != NULL)
    wsk3->nastepny = wsk1;
  if(wsk2 != NULL)
    wsk3->nastepny = wsk2;
  return pierwszy;
}

/* pierwszy to wskaznik na pierwszy wezel listy ktora chcemy posortowac */
/* funkcja zwraca wskaznik na pierwszy wezel posortowanej listy */
/* tryb == 1 - sortowanie po identyfikatorach, tryb == 2 - sortowanie po imionach */
/* tryb == 3 - sortowanie po nazwiskach */
wezel* sortowanie_przez_scalanie(wezel *pierwszy, int n, int tryb)
{
  int i, srodek;
  wezel *wezelwsk, *temp;
  wezel *pierwszy1, *pierwszy2;

  if(n == 1)
    return pierwszy;

  srodek = (int) floor(n/2);
  wezelwsk = pierwszy;
  for(i = 1; i <= srodek-1; i++)
    wezelwsk = wezelwsk->nastepny;
  temp = wezelwsk->nastepny;
  wezelwsk->nastepny = NULL;

  pierwszy1 = sortowanie_przez_scalanie(pierwszy, srodek, tryb);
  pierwszy2 = sortowanie_przez_scalanie(temp, n-srodek, tryb);
  return scalanie_list(pierwszy1, pierwszy2, tryb);
}

/******************** wczytywanie danych z klawiatury ***********************/

/* wczytywanie dowolnych danych w programie
napis jest komunikatem wystwietalnym za kazdym razem gdy uzytkownik
poda zla wartosc, kryterium sprawdza czy podana wartosc jest prawidlowa
jesli typ_danych == 'i' to wczytujemy liczby
jesli typ_danych == 's' to wczytujemy napisy */
void wczytywanie(char *napis, bool (*kryterium)(char*), char typ_danych,
                 void *wynik)
{
  int err;
  char dane[32]; // wczytywane liczby i napisy trzymamy na poczatku
  bool poprawna_wartosc = false; // w stringu dane
  while(!poprawna_wartosc)
  {
    printf("%s", napis);
    err = scanf("%s", dane);
    if(err == -1) printf("blad - znak konca pliku\n");
    else if(err == 0) // scanf nie wczytal poprawnie wartosci
    {// to sie raczej nie powinno wydarzyc bo napisy zawsze sie dobrze wczytuja
      printf("podano niewlasciwe dane\n");
      while('\n' != getchar()); // oczyszczamy bufor ze zbednych znakow (liczb)
      continue;
    }

    poprawna_wartosc = kryterium(dane);
    if(poprawna_wartosc == false)
      printf("podano niepoprawne dane\n");
    else break; // np. kod pocztowy 01_99 zamiast 01-111
  }
  if(typ_danych == 'i') *((int*) wynik) = atoi(dane);// konwersja stringu na liczbe
  else strcpy((char*) wynik, dane); /* typ_danych == 's' brak konwersji */
}

/* sprawdzamy czy napis zawiera tylko litery */
bool kryterium_napisowe(char* napis)
{
  int i = 0;
  while(*(napis+i) != '\0')
  {
    if(!isalpha(napis[i])) // funkcja z ctype.h
         return false;
    i++;
  }
  return true;
}

/* sprawdzamy czy napis jest liczba */
bool kryterium_liczbowe(char* napis)
{
  int i = 0;
  while(*(napis+i) != '\0')
  {
    if(!isdigit(napis[i])) // funkcja z ctype.h
         return false;
    i++;
  }
  return true;
}

/* kryterium uzywane do sprawdzania czy stopien znajomosci */
/* miedzy osobami miesci sie w przedziale <1, 10> */
bool kryterium_wagowe(char* dane)
{
  int liczba;

  if(kryterium_liczbowe(dane))
    liczba = atoi(dane);
  else
    return false;

  if(liczba < 1 || 10 < liczba)
    return false;

  return true;
}

/* kryterium do funkcji main */
bool kryterium1(char* dane)
{
  int liczba;

  if(kryterium_liczbowe(dane))
    liczba = atoi(dane);
  else
    return false;

  return liczba == 1 || liczba == 2 || liczba == 3 || liczba == 4 || liczba == 5 ||
  liczba == 6 || liczba == 7 || liczba == 8 || liczba == 9 || liczba == 10 || liczba == 11;
}

/* kryterium do funkcji sortowanie */
bool kryterium2(char* dane)
{
  int liczba;

  if(kryterium_liczbowe(dane))
    liczba = atoi(dane);
  else
    return false;

  return liczba == 1 || liczba == 2 || liczba == 3;
}

/* kryterium uzywane do wyborow typu tak lub nie */
bool kryterium3(char* dane)
{
  int liczba;

  if(kryterium_liczbowe(dane))
    liczba = atoi(dane);
  else
    return false;

  return liczba == 1 || liczba == 2;
}

// kryterium do sprawdzania czy kod pocztowy zostal poprawnie wpisany
// np. "01-234"
bool kryterium_kod_pocztowy(char* kod)
{
  int i = 0;
  // petla wykonuje sie az napotkamy znak null lub przekroczymy dlugosc
  while((*(kod+i) != '\0') && (i < 6)) // kodu pocztowego
  {
    if(i == 2)
    {
      if(kod[i] != '-') return false;
    }
    else
    {
      if(!(kod[i] >= '0' && kod[i] <= '9')) return false;
    }
    i++;
    if(i == 6 && kod[6] == '\0') return true; // caly kod jest poprawny
  }
  return false;
}

/**************** operacje wejscia, wyjscia z uzyciem plikow ******************/

/* najpierw sa wczytywane glowne informacje o grafie, potem informacje */
/* o wszystkich wezlach, a na koncu informacje o krawedziach miedzy wezlami */
void wczytywanie_bazy(baza *b)
{
  clock_t poczatek, koniec; /* zmienne lokalne sluzace do mierzenia czasu wykonywania danej funkcjonalnosci */
  FILE *plik;
  int id, waga, wybor;
  wezel *wezelwsk, *poprzednik_wezla;
  krawedz *krawedzwsk, *poprzednik_krawedzi;
  bool pierwszy_wezel_dodany = false, pierwsza_krawedz_dodana = false;
  char *tekst =
  "Nacisnij klawisz 1 lub 2\n"
  "1 - wczytywanie przykladowej bazy z pliku\n"
  "2 - wczytywanie bazy zapisanej wczesniej przez uzytkownika (z pliku)\n";
  char pierwsze_imie[32], nazwisko[32], napis[256];

  wczytywanie(tekst, kryterium3, 'i', &wybor);
  poczatek = clock(); /* poczatek pomiaru czasu wykonywania danej funkcjonalnosci */

  switch(wybor)
  {
    case 1:
    if((plik = fopen("przykladowa_baza.txt", "r")) == NULL)
    {
      printf("blad, nie znaleziono pliku zawierajacego ksiazke adresowa\n");
      return ;
    }
    break;
    case 2:
    if((plik = fopen("ksiazka_adresowa.txt", "r")) == NULL)
    {
      printf("blad, nie znaleziono pliku zawierajacego ksiazke adresowa\n");
      return ;
    }
    break;
  }
  /* oczyszczanie bazy z poprzednich danych */
  usuwanie_wszystkich_wezlow(b->zrodlo);
  inicjalizacja_bazy(b);
  printf("Wczytywanie bazy...\n");

  /* wczytywanie glownych informacji o bazie (grafie) z pliku */
  fscanf(plik, "Ksiazka adresowo-spolecznosciowa\n");
  fscanf(plik, "Liczba elementow: %d, biezacy id: %d\n",
          &b->liczba_elementow, &b->biezacy_id);

  /* wczytywanie informacji o kazdym wezle z pliku */
  /* warunek w petli while sprawdza czy w pliku sa jeszcze jakies osoby (wezly) */
  fgets(napis, 256, plik);
  while((sscanf(napis, "Osoba, id %d\n", &id)) > 0)
  {
    wezelwsk = (wezel*) malloc(sizeof(wezel));
    wezelwsk->id = id;
    fscanf(plik, "Dane osobowe:\n");
    fscanf(plik, "%s %s %s nr telefonu: %d\n", wezelwsk->pierwsze_imie,
      wezelwsk->drugie_imie, wezelwsk->nazwisko, &wezelwsk->nr_telefonu);

    fscanf(plik, "Adres:\n");
    fscanf(plik, "Ulica %s %d/%d, kod pocztowy: %7s miasto: %s\n",
      wezelwsk->adres.ulica, &wezelwsk->adres.nr_domu, &wezelwsk->adres.nr_mieszkania,
      wezelwsk->adres.kod_pocztowy, wezelwsk->adres.miasto);

    /* odtwarzamy liste wezlow grafu */
    if(!pierwszy_wezel_dodany)
    {
      b->zrodlo = wezelwsk;
      poprzednik_wezla = b->zrodlo;
      b->zrodlo->nastepny = NULL;
      pierwszy_wezel_dodany = true;
    }
    else
    {
      poprzednik_wezla->nastepny = wezelwsk;
      wezelwsk->nastepny = NULL;
      poprzednik_wezla = wezelwsk;
    }
    fgets(napis, 256, plik);
  }
  fgets(napis, 256, plik); /* wczytujemy znak nowej linii */
  fgets(napis, 256, plik);
  /* wczytujemy informacje o znajomosciach miedzy osobami z pliku */
  wezelwsk = b->zrodlo;
  while(wezelwsk != NULL)
  {
    wezelwsk->pierwszy = NULL;
    fgets(napis, 256, plik);
    while((sscanf(napis, "Id %d %s %s stopien znajomosci: %d\n",
      &id, pierwsze_imie, nazwisko, &waga)) > 0)
    {
      krawedzwsk = (krawedz*) malloc(sizeof(krawedz));
      krawedzwsk->cel = znajdz_wezel(b, id);
      krawedzwsk->waga = waga;
      if(!pierwsza_krawedz_dodana) /* odtwarzamy liste krawedzi danego wezla */
      {
        wezelwsk->pierwszy = krawedzwsk;
        poprzednik_krawedzi = wezelwsk->pierwszy;
        wezelwsk->pierwszy->nastepny = NULL;
        pierwsza_krawedz_dodana = true;
      }
      else
      {
        poprzednik_krawedzi->nastepny = krawedzwsk;
        krawedzwsk->nastepny = NULL;
        poprzednik_krawedzi = krawedzwsk;
      }
      if(fgets(napis, 256, plik) == NULL) break; /* przerywany gdy dojdziemy do konca pliku */
    }
    wezelwsk = wezelwsk->nastepny;
    pierwsza_krawedz_dodana = false;
    if(fgets(napis, 256, plik) == NULL) break; /* przerywany gdy dojdziemy do konca pliku */
  }

  fclose(plik);
  koniec = clock(); /* koniec pomiaru czasu wykonywania danej funkcjonalnosci */
  printf("Calkowity czas wykonywania funkcjonalnosci: %.10f sekund\n",
    (double)(koniec-poczatek)/CLOCKS_PER_SEC);
}

/* najpierw sa zapisywane glowne informacje o grafie, potem informacje */
/* o wszystkich wezlach, a na koncu informacje o krawedziach miedzy wezlami */
void zapisywanie_bazy(baza *b)
{
  clock_t poczatek, koniec; /* zmienne lokalne sluzace do mierzenia czasu wykonywania danej funkcjonalnosci */
  FILE *plik;
  wezel *wezelwsk;
  krawedz *krawedzwsk;

  poczatek = clock(); /* poczatek pomiaru czasu wykonywania danej funkcjonalnosci */
  printf("Zapisywanie bazy do pliku ksiazka_adresowa.txt\n");
  plik = fopen("ksiazka_adresowa.txt", "w");

  /* zapisywanie glownych informacji o bazie (grafie) do pliku */
  fprintf(plik, "Ksiazka adresowo-spolecznosciowa\n");
  fprintf(plik, "Liczba elementow: %d, biezacy id: %d\n",
          b->liczba_elementow, b->biezacy_id);
  /* zapisywanie informacji o kazdym wezle do pliku */
  wezelwsk = b->zrodlo;
  while(wezelwsk != NULL)
  {
    fprintf(plik, "\nOsoba, id %d\n", wezelwsk->id);
    fprintf(plik, "Dane osobowe:\n");
    fprintf(plik, "%s %s %s nr telefonu: %d\n", wezelwsk->pierwsze_imie,
      wezelwsk->drugie_imie, wezelwsk->nazwisko, wezelwsk->nr_telefonu);

    fprintf(plik, "Adres:\n");
    fprintf(plik, "Ulica %s %d/%d, kod pocztowy: %s miasto: %s\n",
      wezelwsk->adres.ulica, wezelwsk->adres.nr_domu, wezelwsk->adres.nr_mieszkania,
      wezelwsk->adres.kod_pocztowy, wezelwsk->adres.miasto);

    wezelwsk = wezelwsk->nastepny;
  }
  /* zapisywanie informacji o wszystkich krawedziach do pliku */
  fprintf(plik, "\nInformacje o znajomosciach miedzy osobami\n");
  wezelwsk = b->zrodlo;
  while(wezelwsk != NULL)
  {
    fprintf(plik, "\nZnajomi osoby o identyfikatorze %d:\n", wezelwsk->id);
    krawedzwsk = wezelwsk->pierwszy;
    while(krawedzwsk != NULL)
    {
      fprintf(plik, "Id %d %s %s stopien znajomosci: %d\n",
        krawedzwsk->cel->id, krawedzwsk->cel->pierwsze_imie,
        krawedzwsk->cel->nazwisko, krawedzwsk->waga);
        krawedzwsk = krawedzwsk->nastepny;
    }
    wezelwsk = wezelwsk->nastepny;
  }

  fclose(plik);
  koniec = clock(); /* koniec pomiaru czasu wykonywania danej funkcjonalnosci */
  printf("Calkowity czas wykonywania funkcjonalnosci: %.10f sekund\n",
    (double)(koniec-poczatek)/CLOCKS_PER_SEC);
}

/********************* operacje na ksiazce adresowej ***********************/

/* wszystkie wczytane dane trzymamy na poczatku w zmiennych lokalnych funkcji
   potem przepisujemy je do ksiazki adresowej */
void dodawanie_osoby(baza *b)
{
  clock_t poczatek, koniec; /* zmienne lokalne sluzace do mierzenia czasu wykonywania danej funkcjonalnosci */
  int wybor;
  char pierwsze_imie[32], drugie_imie[32],
  nazwisko[32], ulica[32], miasto[32];
  char kod_pocztowy[7];
  int nr_telefonu, nr_domu, nr_mieszkania;
  char* napis1 = "Podaj pierwsze imie\n";
  char* napis2 = "Nacisnij klawisz\n1 - tak\n2 - nie\n";
  char* napis3 = "Podaj drugie imie\n";
  char* napis4 = "Podaj nazwisko\n";
  char* napis5 = "Podaj numer telefonu\n";
  char* napis6 = "Podaj nazwe ulicy\n";
  char* napis7 = "Podaj numer domu\n";
  char* napis8 = "Podaj numer mieszkania\n";
  char* napis9 = "Podaj kod pocztowy w formacie \"01-234\"\n";
  char* napis10 = "Podaj miasto\n";
  wezel *wezelwsk;
  wezel *nowy;

  printf("dodawanie nowej pozycji\n");

  wczytywanie(napis1, kryterium_napisowe, 's', pierwsze_imie);

  printf("Czy dana osoba ma drugie imie?\n");
  wczytywanie(napis2, kryterium3, 'i', &wybor);
  if(wybor == 1)
    wczytywanie(napis3, kryterium_napisowe, 's', drugie_imie);
  else
    strcpy(drugie_imie, "_");

  wczytywanie(napis4, kryterium_napisowe, 's', nazwisko);
  wczytywanie(napis5, kryterium_liczbowe, 'i', &nr_telefonu);
  // ---------- wczytywanie adresu  ---------- //
  wczytywanie(napis6, kryterium_napisowe, 's', ulica);
  wczytywanie(napis7, kryterium_liczbowe, 'i', &nr_domu);
  wczytywanie(napis8, kryterium_liczbowe, 'i', &nr_mieszkania);
  wczytywanie(napis9, kryterium_kod_pocztowy, 's', kod_pocztowy);
  wczytywanie(napis10, kryterium_napisowe, 's', miasto);
  poczatek = clock(); /* poczatek pomiaru czasu wykonywania danej funkcjonalnosci */

  /* sprawdzanie czy osoba o danym imieniu i nazwisku
  nie istnieje juz w bazie */
  wezelwsk = b->zrodlo;
  while(wezelwsk != NULL)
  {
    if(strcmp(wezelwsk->pierwsze_imie, pierwsze_imie) == 0 &&
      strcmp(wezelwsk->nazwisko, nazwisko) == 0)
    {
      printf("Osoba o danym imieniu i nazwisku istnieje juz w ksiazce adresowej\n");
      printf("Aktualizacja adresu i numeru telefonu\n");

      /* przepisywanie danych*/
      wezelwsk->nr_telefonu = nr_telefonu;
      strcpy(wezelwsk->adres.ulica, ulica);
      wezelwsk->adres.nr_domu = nr_domu;
      wezelwsk->adres.nr_mieszkania = nr_mieszkania;
      strcpy(wezelwsk->adres.kod_pocztowy, kod_pocztowy);
      strcpy(wezelwsk->adres.miasto, miasto);
      return ;
    }
    wezelwsk = wezelwsk->nastepny;
  }
  /* wczytana osoba nie istnieje w bazie  */
  b->liczba_elementow++;
  nowy = dodawanie_wezla(b, b->biezacy_id);
  b->biezacy_id = (b->biezacy_id+1) % INT_MAX;
  /* przepisywanie danych*/
  strcpy(nowy->pierwsze_imie, pierwsze_imie);
  strcpy(nowy->drugie_imie, drugie_imie);
  strcpy(nowy->nazwisko, nazwisko);
  nowy->nr_telefonu = nr_telefonu;
  strcpy(nowy->adres.ulica, ulica);
  nowy->adres.nr_domu = nr_domu;
  nowy->adres.nr_mieszkania = nr_mieszkania;
  strcpy(nowy->adres.kod_pocztowy, kod_pocztowy);
  strcpy(nowy->adres.miasto, miasto);

  koniec = clock(); /* koniec pomiaru czasu wykonywania danej funkcjonalnosci */
  printf("Calkowity czas wykonywania funkcjonalnosci: %.10f sekund\n",
    (double)(koniec-poczatek)/CLOCKS_PER_SEC);
}

void usuwanie_osoby(baza *b)
{
  int id = -1;
  clock_t poczatek, koniec; /* zmienne lokalne sluzace do mierzenia czasu wykonywania danej funkcjonalnosci */
  char* napis = "Podaj identyfikator osoby ktora chcesz usunac z bazy\n";
  wezel *usuwany;

  wczytywanie(napis, kryterium_liczbowe, 'i', &id);
  poczatek = clock(); /* poczatek pomiaru czasu wykonywania danej funkcjonalnosci */

  /* sprawdzanie czy osoba o podanym id istnieje w bazie */
  if((usuwany = znajdz_wezel(b, id)) == NULL)
    printf("Osoba o danym identyfikatorze nie wsytepuje w bazie\n");
  else
  {/* osoba o podanym przez uzytkownika id istnieje w bazie */
    usuwanie_wezla(b, id);
    b->liczba_elementow--;
    printf("Osoba usunieta\n");
  }

  koniec = clock(); /* koniec pomiaru czasu wykonywania danej funkcjonalnosci */
  printf("Calkowity czas wykonywania funkcjonalnosci: %.10f sekund\n",
    (double)(koniec-poczatek)/CLOCKS_PER_SEC);
}

void sortowanie(baza *b)
{
  int wybor;
  clock_t poczatek, koniec;/* zmienne lokalne sluzace do mierzenia czasu wykonywania danej funkcjonalnosci */
  char *napis =
  "Nacisnij klawisz 1, 2 lub 3\n"
  "1 - sortowanie po identyfikatorach\n"
  "2 - sortowanie po pierwszych imionach\n"
  "3 - sortowanie po nazwiskach\n";

  if(b->liczba_elementow == 0)
  {
    printf("Baza jest pusta, brak poztcji do sortowania\n");
    return ;
  }
  wczytywanie(napis, kryterium2, 'i', &wybor);
  poczatek = clock(); /* poczatek pomiaru czasu wykonywania danej funkcjonalnosci */
  printf("Sortowanie...\n");
  switch(wybor)
  {
    case 1:
      b->zrodlo = sortowanie_przez_scalanie(b->zrodlo, b->liczba_elementow, 1);
    break;
    case 2:
      b->zrodlo = sortowanie_przez_scalanie(b->zrodlo, b->liczba_elementow, 2);
    break;
    case 3:
      b->zrodlo = sortowanie_przez_scalanie(b->zrodlo, b->liczba_elementow, 3);
    break;
  }

  koniec = clock(); /* koniec pomiaru czasu wykonywania danej funkcjonalnosci */
  printf("Calkowity czas wykonywania funkcjonalnosci: %.10f sekund\n",
    (double)(koniec-poczatek)/CLOCKS_PER_SEC);
}

/* wypisywanie bazy posortowanej wzgledem nazwisk */
void wypisywanie_bazy(baza *b)
{
  clock_t poczatek, koniec; /* zmienne lokalne sluzace do mierzenia czasu wykonywania danej funkcjonalnosci */
  wezel *wezelwsk;
  krawedz *krawedzwsk;

  poczatek = clock(); /* poczatek pomiaru czasu wykonywania danej funkcjonalnosci */

  printf("Wypisywanie bazy posortowanej wzgledem nazwisk osob:\n");
  /* ponizej sortowanie po nazwiskach, szczegoly w czesci "sortowanie" */
  b->zrodlo = sortowanie_przez_scalanie(b->zrodlo, b->liczba_elementow, 3);


  wezelwsk = b->zrodlo;
  while(wezelwsk != NULL)
  {
    printf("Id = %d\nImiona: %s %s, Nazwisko: %s\n", wezelwsk->id,
      wezelwsk->pierwsze_imie, wezelwsk->drugie_imie, wezelwsk->nazwisko);
    printf("Adres:\n");
    printf("ulica %s %d/%d, kod pocztowy: %s, miasto: %s\n",
      wezelwsk->adres.ulica, wezelwsk->adres.nr_domu, wezelwsk->adres.nr_mieszkania,
      wezelwsk->adres.kod_pocztowy, wezelwsk->adres.miasto);
    printf("nr telefonu: %d\n\n", wezelwsk->nr_telefonu);
    printf("Znajomi osoby:\n");
    krawedzwsk = wezelwsk->pierwszy;
    while(krawedzwsk != NULL)
    {
      printf("id %d, %s %s, stopien znajomosci: %d\n", krawedzwsk->cel->id,
        krawedzwsk->cel->pierwsze_imie, krawedzwsk->cel->nazwisko, krawedzwsk->waga);
      krawedzwsk = krawedzwsk->nastepny;
    }
    printf("\n");
    wezelwsk = wezelwsk->nastepny;
  }

  koniec = clock(); /* koniec pomiaru czasu wykonywania danej funkcjonalnosci */
  printf("Calkowity czas wykonywania funkcjonalnosci: %.10f sekund\n",
    (double)(koniec-poczatek)/CLOCKS_PER_SEC);
}

void dodawanie_znajomosci(baza *b)
{
  int id1, id2, wynik, stopien_znajomosci1, stopien_znajomosci2;
  clock_t poczatek, koniec; /* zmienne lokalne sluzace do mierzenia czasu wykonywania danej funkcjonalnosci */
  char* napis1 = "Podaj identyfikator pierwszej osoby\n";
  char* napis2 = "Podaj identyfikator drugiej osoby\n";
  char* napis3 = "Podaj stopien w jakim pierwsza osoba zna osobe druga\n";
  char* napis4 = "Podaj stopien w jakim druga osoba zna osobe pierwsza\n";
  wezel *wsk1, *wsk2;

  printf("Dodawanie znajomosci miedzy dwiema osobami\n");

  wczytywanie(napis1, kryterium_liczbowe, 'i', &id1);
  if((wsk1 = znajdz_wezel(b, id1)) == NULL)
  {
    printf("Osoba o podanym identyfikatorze nie istnieje w bazie\n");
    return ;
  }
  wczytywanie(napis2, kryterium_liczbowe, 'i', &id2);
  if((wsk2 = znajdz_wezel(b, id2)) == NULL)
  {
    printf("Osoba o podanym identyfikatorze nie istnieje w bazie\n");
    return ;
  }
  if(id1 == id2)
  {
    printf("Identyfikator pierwszej osoby jest rowny identyfikatorowi drugiej\n");
    printf("Funkcja dodaje znajomosc miedzy dwoma roznymi osobami\n");
    return ;
  }

  wczytywanie(napis3, kryterium_wagowe, 'i', &stopien_znajomosci1);
  wczytywanie(napis4, kryterium_wagowe, 'i', &stopien_znajomosci2);
  poczatek = clock(); /* poczatek pomiaru czasu wykonywania danej funkcjonalnosci */

  wynik = dodawanie_krawedzi(b, wsk1, wsk2,
            stopien_znajomosci1, stopien_znajomosci2);

  if(wynik == -2)
    printf("Znajomosc miedzy danymi osobami zostala dodana juz wczesniej\n");
  else
    printf("Znajomosc zostala dodana\n");

  koniec = clock(); /* koniec pomiaru czasu wykonywania danej funkcjonalnosci */
  printf("Calkowity czas wykonywania funkcjonalnosci: %.10f sekund\n",
    (double)(koniec-poczatek)/CLOCKS_PER_SEC);
}

void usuwanie_znajomosci(baza *b)
{
  int id1, id2, wynik;
  clock_t poczatek, koniec; /* zmienne lokalne sluzace do mierzenia czasu wykonywania danej funkcjonalnosci */
  char* napis1 = "Podaj identyfikator pierwszej osoby\n";
  char* napis2 = "Podaj identyfikator drugiej osoby\n";
  wezel *wsk1, *wsk2;

  printf("Usuwanie znajomosci miedzy dwiema osobami\n");

  wczytywanie(napis1, kryterium_liczbowe, 'i', &id1);
  if((wsk1 = znajdz_wezel(b, id1)) == NULL)
  {
    printf("Osoba o podanym identyfikatorze nie istnieje w bazie\n");
    return ;
  }
  wczytywanie(napis2, kryterium_liczbowe, 'i', &id2);
  if((wsk2 = znajdz_wezel(b, id2)) == NULL)
  {
    printf("Osoba o podanym identyfikatorze nie istnieje w bazie\n");
    return ;
  }
  if(id1 == id2)
  {
    printf("Identyfikator pierwszej osoby jest rowny identyfikatorowi drugiej\n");
    printf("Funkcja usuwa znajomosc miedzy dwoma roznymi osobami\n");
    return ;
  }
  poczatek = clock(); /* poczatek pomiaru czasu wykonywania danej funkcjonalnosci */

  wynik = usuwanie_krawedzi(b, id1, id2);

  if(wynik == -2)
    printf("Miedzy danymi osobami nie istniala znajomosc\n");
  else
    printf("Znajomosc zostala usunieta\n");

  koniec = clock(); /* koniec pomiaru czasu wykonywania danej funkcjonalnosci */
  printf("Calkowity czas wykonywania funkcjonalnosci: %.10f sekund\n",
    (double)(koniec-poczatek)/CLOCKS_PER_SEC);
}

void zmiana_stopnia_znajomosci(baza *b)
{
  int id1, id2, stopien_znajomosci;
  clock_t poczatek, koniec; /* zmienne lokalne sluzace do mierzenia czasu wykonywania danej funkcjonalnosci */
  char* napis1 = "Podaj identyfikator pierwszej osoby\n";
  char* napis2 = "Podaj identyfikator drugiej osoby\n";
  char* napis3 = "Podaj stopien w jakim pierwsza osoba zna osobe druga\n";
  wezel *wsk1, *wsk2;

  printf("Zmiana stopnia znajomosci w jakim osoba pierwsza zna druga\n");

  wczytywanie(napis1, kryterium_liczbowe, 'i', &id1);
  if((wsk1 = znajdz_wezel(b, id1)) == NULL)
  {
    printf("Osoba o podanym identyfikatorze nie istnieje w bazie\n");
    return ;
  }
  wczytywanie(napis2, kryterium_liczbowe, 'i', &id2);

  if((wsk2 = znajdz_wezel(b, id2)) == NULL)
  {
    printf("Osoba o podanym identyfikatorze nie istnieje w bazie\n");
    return ;
  }

  if(id1 == id2)
  {
    printf("Identyfikator pierwszej osoby jest rowny identyfikatorowi drugiej\n");
    printf("Funkcja zmienia stopien znajomosci miedzy dwoma roznymi osobami\n");
    return ;
  }

  wczytywanie(napis3, kryterium_wagowe, 'i', &stopien_znajomosci);
  poczatek = clock(); /* poczatek pomiaru czasu wykonywania danej funkcjonalnosci */

  if(zmiana_wagi_krawedzi(b, wsk1, wsk2, stopien_znajomosci) == -1)
    printf("Osoby o podanych identyfikatorach nie znaja sie\n");
  else
    printf("stopien znajomosci zmieniony\n");

  koniec = clock(); /* koniec pomiaru czasu wykonywania danej funkcjonalnosci */
  printf("Calkowity czas wykonywania funkcjonalnosci: %.10f sekund\n",
    (double)(koniec-poczatek)/CLOCKS_PER_SEC);
}

/* rekurencyjna funkcja wypisujaca sciezke od wezla zrodlowego */
/* do wezla docelowego za pomoca zmiennej skladowej wezla "poprzednik" */
void wypisywanie_najkrotszej_sciezki(wezel *wezelwsk)
{
  if(wezelwsk->poprzednik == NULL)
    printf("id %d %s %s\n", wezelwsk->id,
      wezelwsk->pierwsze_imie, wezelwsk->nazwisko);
  else
  {
    wypisywanie_najkrotszej_sciezki(wezelwsk->poprzednik);
    printf("id %d %s %s\n", wezelwsk->id,
      wezelwsk->pierwsze_imie, wezelwsk->nazwisko);
  }
}

/* funkcja szukajaca najszybszej lub najskuteczniejszej sciezki */
/* za pomoca algorytmu Dijkstry */
void najkrotsza_sciezka(baza *b)
{
  int id1, id2, tryb;
  clock_t poczatek, koniec; /* zmienne lokalne sluzace do mierzenia czasu wykonywania danej funkcjonalnosci */
  char* napis1 = "Nacisnij klawisz 1 lub 2\n"
  "1 - Wyszukiwanie najszybszego sposobu na nawiazanie znajomosci\n"
  "miedzy dwoma osobami (najmniejsza liczba posrednikow)\n"
  "2 - Wyszukiwanie najskuteczniejszego sposobu na nawiazanie znajomosci\n"
  "miedzy dwoma osobami (poprzez osoby, ktore sie najbardziej znaja)\n";
  char* napis2 = "Podaj identyfikator pierwszej osoby\n";
  char* napis3 = "Podaj identyfikator drugiej osoby\n";
  wezel *wsk1, *wsk2, *wezelwsk;

  wczytywanie(napis1, kryterium3, 'i', &tryb);

  wczytywanie(napis2, kryterium_liczbowe, 'i', &id1);
  if((wsk1 = znajdz_wezel(b, id1)) == NULL)
  {
    printf("Osoba o podanym identyfikatorze nie istnieje w bazie\n");
    return ;
  }
  wczytywanie(napis3, kryterium_liczbowe, 'i', &id2);
  poczatek = clock(); /* poczatek pomiaru czasu wykonywania danej funkcjonalnosci */

  if((wsk2 = znajdz_wezel(b, id2)) == NULL)
  {
    printf("Osoba o podanym identyfikatorze nie istnieje w bazie\n");
    return ;
  }
  if(id1 == id2)
  {
    printf("Identyfikator pierwszej osoby jest rowny identyfikatorowi drugiej\n");
    printf("Funkcja szuka drogi miedzy dwoma roznymi osobami\n");
    return ;
  }

  if((wezelwsk = algorytm_dijkstry(b, wsk1, wsk2, tryb)) == NULL)
    printf("miedzy podanymi osobami nie istnieje "
           "sposob na nawiazanie znajomosci\n");
  else
    wypisywanie_najkrotszej_sciezki(wezelwsk);

  koniec = clock(); /* koniec pomiaru czasu wykonywania danej funkcjonalnosci */
  printf("Calkowity czas wykonywania funkcjonalnosci: %.10f sekund\n",
    (double)(koniec-poczatek)/CLOCKS_PER_SEC);

}

void zwalnianie_pamieci(baza *b)
{
  usuwanie_wszystkich_wezlow(b->zrodlo);
  free(b);
}

/***************************** main **********************************/

int main()
{
  baza *b = (baza *) malloc(sizeof(baza));
  int wybor = 0;
  char *napis1 =
  "\nWybierz operacje\n"
  "(poprzez nacisniecie klawisza 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 lub 11)\n"
  "1 - Dodawanie nowej osoby do ksiazki adresowej\n"
  "2 - Usuwanie osoby z ksiazki adresowej\n"
  "3 - Dodawanie znajomosci miedzy osobami\n"
  "4 - Usuwanie znajomosci miedzy osobami\n"
  "5 - Zmiana stopnia znajomosci miedzy osobami\n"
  "6 - Wczytywanie bazy z pliku\n"
  "7 - Zapisywanie bazy do pliku\n"
  "8 - Wypisywanie ksiazki adresowej na ekran\n"
  "9 - Wypisywanie sposobu na nawiazanie kontaktu miedzy osobami\n"
  "10 - Sortowanie ksiazki adresowej\n"
  "11 - Koniec\n";

  printf("Program - ksiazka adresowo - spolecznosciowa\n");
  printf("autor: Pawel Ostaszewski\n");

  inicjalizacja_bazy(b);

  while(wybor != 11)
  {
    wczytywanie(napis1, kryterium1, 'i', &wybor);
    switch(wybor)
    {
      case 1:
        dodawanie_osoby(b);
        break;
      case 2:
        usuwanie_osoby(b);
        break;
      case 3:
        dodawanie_znajomosci(b);
        break;
      case 4:
        usuwanie_znajomosci(b);
        break;
      case 5:
        zmiana_stopnia_znajomosci(b);
        break;
      case 6:
        wczytywanie_bazy(b);
        break;
      case 7:
        zapisywanie_bazy(b);
        break;
      case 8:
        wypisywanie_bazy(b);
        break;
      case 9:
        najkrotsza_sciezka(b);
        break;
      case 10:
        sortowanie(b);
        break;
      case 11:
        break;
    }
  }
  zwalnianie_pamieci(b);
  return 0;
}
