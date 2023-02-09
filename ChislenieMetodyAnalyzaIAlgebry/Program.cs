﻿using System;
using System.Collections.Generic;
using System.Linq;

namespace Algorithms
{
    internal abstract class Maths
    {
        /// <summary>
        /// Метод Гаусса (Решение СЛАУ)
        /// </summary>
        /// <param name="matrix">Начальная матрица</param>
        /// <returns></returns>
        public static double[] Gauss(double[,] matrix)
        {
            int n = matrix.GetLength(0); //Размерность
            double[,] matrixClone = new double[n, n + 1];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n + 1; j++)
                    matrixClone[i, j] = matrix[i, j];

            // Прямой ход
            for (int k = 0; k < n; k++) //k-номер строки
            {
                for (int i = 0; i < n + 1; i++)//i-номер столбца
                {
                    var c = (((i-1)!=-1)||(i+1)>=(n))?(i-1):(i+1);
                   if(matrix[k,k]==0)
                   {
                       double[] temp = new double[n];
                       for(int r=0;r<n;r++)
                       {
                           temp[r] = matrixClone[r,i];
                           matrixClone[r, i] = matrixClone[r, c];
                           matrixClone[r, c] = temp[r];
                           for (int y = 0; y < n; y++) //Обновление
                           for (int j = 0; j < n + 1; j++)
                               matrix[y, j] = matrixClone[y, j];

                       }
                       matrixClone[k, i] = matrixClone[k, i] / matrixClone[k, k]; //Деление k-строки на первый член
                   }
                   else {
                       matrixClone[k, i] = matrixClone[k, i] / matrix[k, k]; //Деление k-строки на первый член
                   }

                }

                for (int i = k + 1; i < n; i++) //i-номер следующей строки после k
                {
                    double conf = matrixClone[i, k] / matrixClone[k, k]; //Коэффициент
                    for (int j = 0; j < n + 1; j++) //j-номер столбца следующей строки после k
                        matrixClone[i, j] = matrixClone[i, j] - matrixClone[k, j] * conf; //Зануление элементов матрицы ниже первого члена, преобразованного в единицу
                }
                for (int i = 0; i < n; i++) //Обновление
                    for (int j = 0; j < n + 1; j++)
                        matrix[i, j] = matrixClone[i, j];
            }

            // Обратный ход
            for (int k = n - 1; k > -1; k--) //k-номер строки
            {
                for (int i = n; i > -1; i--) //i-номер столбца
                {
                  matrixClone[k, i] = matrixClone[k, i] / matrix[k, k];
                }

                for (int i = k - 1; i > -1; i--) //i-номер следующей строки после k
                {
                    double conf = matrixClone[i, k] / matrixClone[k, k];
                    for (int j = n; j > -1; j--) //j-номер столбца следующей строки после k
                        matrixClone[i, j] = matrixClone[i, j] - matrixClone[k, j] * conf;
                }
            }

            // Отделяем от общей матрицы ответы
            double[] answer = new double[n];
            for (int i = 0; i < n; i++)
                answer[i] = matrixClone[i, n];

            return answer;
        }

        public static double[] Thomas(double[,] matrix)
        {
          int n = matrix.GetLength(0); //Размерность
          if( n+1 != matrix.GetLength(1)) //Условие размерности
          {
              Console.WriteLine("Array doesn't fit to this method");
              return null;
          }
          double[,] matrixA = new double[n, n];
          for (int i = 0; i < n; i++)
              for (int j = 0; j < n; j++)
                  matrixA[i, j] = matrix[i, j];

          double[] matrixB = new double[n];
            for (int i = 0; i < n; i++)
              matrixB[i]=matrix[i,n];

          for(int i=1;i<n-1;i++)
          {
            for(int j=1;j<n-1;j++)
            {
              if(matrixA[i,i] < Math.Abs(matrixA[i,i-1])+Math.Abs(matrixA[i,i+1]))
              {
                Console.WriteLine("Array doesn't fit to this method");
                return matrixB;
              }
              if(matrixA[i,i]==0)
              {
                Console.WriteLine("Array doesn't fit to this method");
                return matrixB;
              }
            }
          }

          double[] u = new double[n];
          double[] v = new double[n];

          //Первая строка матрицы
          v[0] = matrixA[0,1]/(-matrixA[0,0]);
          u[0] = -matrixB[0]/(-matrixA[0,0]);

          //После первой до n-1 строки матрицы
          for(int i=1; i<n-1;i++)
          {
            v[i]= matrixA[i,i+1]/(-matrixA[i,i]-matrixA[i,i-1]*v[i-1]);
            u[i]= (matrixA[i,i-1]*u[i-1]-matrixB[i])/(-matrixA[i,i]-matrixA[i,i-1]*v[i-1]);
          }
          //Последняя строка матрицы
          v[n-1]=0;
          u[n-1]=(matrixA[n-1,n-2]*u[n-2]-matrixB[n-1])/(-matrixA[n-1,n-1]-matrixA[n-1,n-2]*v[n-2]);


                  // Отделяем от общей матрицы ответы
                  double[] answer = new double[n];
                  answer[n-1]=u[n-1];
                  for (int i = n-1; i > 0; i--)
                      answer[i-1] =v[i-1]*answer[i]+u[i-1];

                  return answer;
        }

        public static double SinTailor(int a, double n)
        {
          double result=0;
          for(int i=0; i<a; i++)
          {
            result += (Math.Pow(-1,i)*Math.Pow(n,(2*i+1)))/Factorial(2*i+1);
          }
          return result;
        }

        private static int Factorial(int n)
        {
            if (n == 1) return 1;

            return n * Factorial(n - 1);
        }

        public static double[] Iteration(double[,] matrix, double e)
        {
          var n = matrix.GetLength(0); //Строки
          var m = matrix.GetLength(1); //Столбцы + В
          
          var sumOfLine = new double[n];
          Fill(sumOfLine,0);
          for(var i=0;i<n;i++)
            for(var j=0;j<m-1;j++)
              sumOfLine[i] += matrix[i,j]; //Сумма элементов для каждой строки

          for(var i=0;i<n;i++)
          {
              var lineOfMatrix = new double[m - 1];
              for (var j = 0; j < m - 1; j++)
                  lineOfMatrix[j] = Math.Abs(matrix[i, j]); //Копируем абсолютные значения элементов i-ой строки
              
              var maxNum = lineOfMatrix.Max(); //Получаем элемент i-ой строки с максимальным значением
              var indexOfMaxNum = lineOfMatrix.ToList().IndexOf(maxNum); //Получаем индекс этого элемента
              if (!(Math.Abs(maxNum - matrix[i, i]) > 0) || indexOfMaxNum == i) continue; //Если максимальный элемент и так равен i-ому элементу i-ой строки, то идём на следующую 
              
              for (var p = 0; p < m; p++)
                  (matrix[i, p], matrix[indexOfMaxNum, p]) = (matrix[indexOfMaxNum, p], matrix[i, p]); //Меняем строки местами так, чтобы максимальный элемент i-ой строки стал диагональным в матрице
          }

          var matrixA = new double[n, n];
          for (var i = 0; i < n; i++)
            for (var j = 0; j < n; j++)
              matrixA[i, j] = matrix[i, j];

          var matrixB = new double[n];
          for (var i = 0; i < n; i++)
              matrixB[i]=matrix[i,n];
          
          var answer = new double[n];
          var temp = new double[n];
          Fill(answer,0); Fill(temp, 0);
          do
          {
              for (var i = 0; i < n; i++)
              {
                  answer[i] = matrixB[i]/matrix[i,i];
                  for (var j = 0; j < m - 1; j++)
                  {
                      if (i == j) continue;
                      answer[i] -= matrixA[i, j]/matrix[i,i] * temp[j];
                  }
              }
              for (var p = 0; p <n; p++)
                  if (Math.Abs(answer[p] - temp[p]) < e) return answer;
              
              for (var k = 0; k <n; k++)
                  temp[k] = answer[k];
          } while (true);
        }

        private static void Fill<T>(IList<T> array, T value)
        {
            for (var i = 0; i < array.Count; i++)
            {
                array[i] = value;
            }
        }
    }
}


internal abstract class Program
{
    public static void Main()
    {
        Console.WriteLine("Enter size of matrix"); var n = Convert.ToInt32(Console.ReadLine());
        var matrixText = System.IO.File.ReadAllText(@"C:\Users\Valerok\RiderProjects\Program\ChislenieMetodyAnalyzaIAlgebry\matrix.txt");
        var matrix = new double[n, n+1];
        var line = 0;
        foreach (var row in matrixText.Split('\n'))
        {
            var column = 0;
            foreach (var col in row.Trim().Split(' '))
            {
                matrix[line, column] = double.Parse(col.Trim());
                column++;
            }
            line++;
        }
        
        for (var k = 0; k < n; k++)
        {
            for (var i = 0; i < (n + 1); i++)
            {
                Console.Write(matrix[k,i]+" ");
            } Console.Write("\n");
        } //Создаём и печатаем новую матрицу
    
        var answer = Algorithms.Maths.Iteration(matrix, 0.00000000001);
        for(var i=0;i<n;i++)
            Console.WriteLine("x"+(i+1)+" : "+answer[i]);

    }
}