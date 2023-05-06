import cv2
import numpy as np
import matplotlib.pyplot as plt

# Lecture de l'image
img = cv2.imread('puzzle.png')

# Correction gamma
gamma = 2.2
gamma = np.uint8(255 * (img / 255) ** gamma)


# Flou gaussien
flou = cv2.GaussianBlur(gamma, (3,3), 0)

# Masque noir et blanc
lower = np.array([0, 17, 80])     ##[B value, G value, R value]
upper = np.array([25,60,190]) 
mask = cv2.inRange(flou, lower, upper)

# Nombre d'itérations
it = 3

kernel = cv2.getStructuringElement(cv2.MORPH_ELLIPSE, (3,3))

# Ouverture morphologique pour boucher les trous
closed = cv2.morphologyEx(mask, cv2.MORPH_OPEN, kernel, iterations=it)

# Dilatation
dilated = cv2.dilate(closed, kernel, iterations=it)

# Érosion
eroded = cv2.erode(dilated, kernel, iterations=it)

# ajout ligne blanche bords bas et haut
for x in range (eroded.shape[1]-1):
    for i in range (5):
        eroded[i,x]= 255
        eroded[eroded.shape[0]-1-i,x]= 255

# Trouver les contours
contours, hierarchy = cv2.findContours(image=eroded, mode=cv2.RETR_TREE , method=cv2.CHAIN_APPROX_SIMPLE)


# Dessiner les contours
cv2.drawContours(image=img, contours=contours, contourIdx=-1, color=(0, 255, 0), thickness=2, lineType=cv2.LINE_AA)

# Faire des contours simplifiés
tmp = 0
for contour in contours:
    if (tmp > 0):
        convexHull = cv2.convexHull(contour)
        cv2.drawContours(image=img, contours=[convexHull], contourIdx=-1, color=(0, 0, 255), thickness=2, lineType=cv2.LINE_AA)

    tmp+=1
    


# Affichage de l'image
cv2.imshow('gamma', gamma)
cv2.imshow('Binaire', eroded)
cv2.imshow('Contours', img)
cv2.waitKey(0)
cv2.destroyAllWindows()