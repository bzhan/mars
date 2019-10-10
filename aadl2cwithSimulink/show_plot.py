import csv
import matplotlib.pyplot as plt

data = []
with open('output.csv') as csvDataFile:
    csvReader = csv.reader(csvDataFile)
    for row in csvReader:
        data.append([float(row[0])*10+100, float(row[1])])

# Plot the data
plt.plot(data)

# Show the plot
plt.show()
